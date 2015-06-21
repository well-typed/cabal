module Distribution.Client.Dependency.ExternalSMT
  ( SVersion,
    SConstraint,
    SDepConstraints,
    SPackage(..),

    VersionSymbolMap,
    SymbolVersionMap,
    VersionMappings,

    ResolvedInstance,

    InstanceVersion,
    getVersion,
    isSourceInstance,
    isInstalledInstance,

    depToSConstraint,
    pkgConstraintToSConstraint,

    externalSMTResolver,

    toPackageIds,
    prettyPackageId,

    constraintPkgName,
    installedIdtoDep
  ) where


import Distribution.Client.Dependency.Modular.Solver
  ( SolverConfig(..) )
import Distribution.Client.Dependency.Types
  ( DependencyResolver, Progress(..), PackageConstraint(..) )
import Distribution.System
  ( Platform(..) )
import Distribution.Client.Types
  ( SourcePackage(..) )
import qualified Distribution.PackageDescription as PD
  ( GenericPackageDescription(..),
    PackageDescription(..),    
    Library(..),
    BuildInfo(..),
    CondTree(..) )
import qualified Distribution.Simple.PackageIndex as PI
import Distribution.InstalledPackageInfo
  ( InstalledPackageInfo_(..) )
import Distribution.Package
    ( PackageName(..),
      Dependency(..),
      PackageIdentifier(..),
      InstalledPackageId(..),
      packageVersion )
import Distribution.Client.PackageIndex
  ( lookupPackageName )
import Distribution.Version
import Data.Version ( parseVersion )

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe, fromJust, mapMaybe)
import Data.List
import Data.List.Split
import Text.ParserCombinators.ReadP (readP_to_S)
import Data.Function (on)

import Data.SBV

import Debug.Trace (trace)


-- | symbolic package version
type SVersion = SWord32

-- | resolved package instance
type ResolvedInstance = (PackageName, Word32)

-- | symbolic package instance constraints
type SConstraint = SVersion -> SBool

type SDepConstraints = M.Map PackageName [SConstraint]

data SPackage = SPackage {
  spkgName            :: PackageName,
  spkgNumInstances    :: SWord32,
  spkgConstraints     :: [SConstraint],
  spkgSDepConstraints :: [SDepConstraints],
  spkgSVersion        :: SVersion
}


type VersionSymbolMap = M.Map InstanceVersion SVersion
type SymbolVersionMap = M.Map Word32 InstanceVersion
type VersionMappings  = M.Map PackageName (VersionSymbolMap, SymbolVersionMap)


data InstanceVersion = SI Version
                     | II Version
                       deriving (Show, Eq)

instance Ord InstanceVersion where
  (SI x) `compare` (SI y) = x `compare` y
  (II x) `compare` (II y) = x `compare` y
  (SI x) `compare` (II y)
    | x == y    = LT
    | otherwise = x `compare` y
  (II x) `compare` (SI y)
    | x == y    = GT
    | otherwise = x `compare` y

getVersion :: InstanceVersion -> Version
getVersion (SI v) = v
getVersion (II v) = v

isSourceInstance :: InstanceVersion -> Bool
isSourceInstance (SI _) = True
isSourceInstance _      = False

isInstalledInstance :: InstanceVersion -> Bool
isInstalledInstance (II _) = True
isInstalledInstance _      = False


depToSConstraint :: VersionMappings -> Dependency -> SConstraint
depToSConstraint vms (Dependency pn vr) = mkConstraint vr
  where
    mkConstraint (UnionVersionRanges vr1 vr2) =
      \s -> mkConstraint vr1 s ||| mkConstraint vr2 s
    mkConstraint (IntersectVersionRanges vr1 vr2) =
      \s -> mkConstraint vr1 s &&& mkConstraint vr2 s
    mkConstraint (VersionRangeParens vr') = mkConstraint vr'
    mkConstraint vr =
      let vs = map snd
             $ filter ((`withinRange` vr) . getVersion . fst) (M.toList vts)
      in if null vs
         then const false
         else \s -> s .>= head vs &&& s .<= last vs

    -- TODO: fix fromJust
    (vts, _) = fromJust $ M.lookup pn vms


pkgConstraintToSConstraint :: VersionMappings -> PackageConstraint -> SConstraint
pkgConstraintToSConstraint vms = mkConstraint
  where
    mkConstraint (PackageConstraintVersion pn vr) =
      depToSConstraint vms (Dependency pn vr)
    mkConstraint (PackageConstraintInstalled pn) =
      \s -> bAny (.== s) (versionsBy isInstalledInstance pn)
    mkConstraint (PackageConstraintSource pn) =
      \s -> bAny (.== s) (versionsBy isSourceInstance pn)
    mkConstraint _ = const true

    versionsBy f pn = maybe [] (map snd . filter (f . fst) . M.toList . fst)
                               (M.lookup pn vms)    


-- | validate an install plan model
valid :: S.Set PackageName -> [SPackage] -> SBool
valid targets spkgs = bAll checkPkg spkgs
  where
    checkPkg (SPackage pn ni pcs _ ver)
      | pn `S.member` targets = ver ./= 0 &&& validPkg pn ni pcs ver
      | otherwise             = isNeeded pn ver &&& validPkg pn ni pcs ver
    validPkg pn ni pcs ver = rangeFine ni ver
                         &&& checkConstraints ver pcs
                         &&& checkDepConstraints pn ver
    rangeFine ni ver = ver .>= 0 &&& ver .<= ni
    checkConstraints ver cs = bAll ($ ver) cs
    isNeeded pn ver = ite (bAny (requires pn ver) spkgs) (ver ./= 0) (ver .== 0)
    requires pn ver (SPackage _ _ _ dcs ver') =
      ver' ./= 0 &&&
      bOr (zipWith (\v dcs' -> v .== ver' &&&
                     if pn `M.member` dcs' then true else false
                   ) [1..] dcs)
    checkDepConstraints pn ver = bAll (checkPkgDepConstraints pn ver) spkgs
    checkPkgDepConstraints pn ver (SPackage _ _ _ dcs ver') =
      ver' .== 0 |||
      bOr (zipWith (\v dcs' -> v .== ver' &&&
                     bAll ($ ver) (maybe [] ((./= 0) :) $ M.lookup pn dcs')
                   ) [1..] dcs)


solveSMT :: S.Set PackageName
         -> [PackageName]
         -> [SWord32]
         -> [[SConstraint]]
         -> [[SDepConstraints]]
         -> IO [ResolvedInstance]
solveSMT targets pns nis pcs dcs = do
  model <- getModel <$> sat ( (valid targets . mkSPkgs) <$>
                              mkExistVars (length pns) )
  case model of
    Right (_, sln) -> return $ zip pns sln
    Left  m        -> return []
  --model <- maximize Quantified sum (length pns) (valid targets . mkSPkgs)
  --return $ maybe [] (zip pns) model
  where
    mkSPkgs = zipWith5 SPackage pns nis pcs dcs


-- TODO: - flags, stanzas, etc
externalSMTResolver :: SolverConfig -> DependencyResolver
externalSMTResolver sc (Platform arch os) cinfo iidx sidx pprefs pcs pns = do
  sln <- solveSMT (S.fromList pns) allTargets nis pcs' dcs
  let sln' = toPackageIds vms sln
  print $ map prettyPackageId sln'
  return $ Fail "not fully implemented yet"
  where
    nis :: [SWord32]
    nis = map (fromIntegral . length . pkgInstances) allTargets

    pcs' :: [[SConstraint]]
    pcs' = map (map (pkgConstraintToSConstraint vms) . groupConstraints)
               allTargets

    groupConstraints :: PackageName -> [PackageConstraint]
    groupConstraints pn = filter (\pc -> pn == constraintPkgName pc) pcs


    dcs :: [[SDepConstraints]]
    dcs = map ( map (M.fromList
              . map (\d -> (depname d, [depToSConstraint vms d])))
              . buildDeps ) allTargets

    vms :: VersionMappings
    vms = M.fromList
        $ zip allTargets
        $ map (mkVersionMaps . pkgInstances) allTargets

    allTargets :: [PackageName]
    allTargets = S.toList $ depdfs S.empty pns

    depname (Dependency pkgname _) = pkgname

    mkVersionMaps vs = (M.fromList $ zip vs [1..], M.fromList $ zip [1..] vs)

    pkgInstances pn = sort $ map (II . fst) (PI.lookupPackageName iidx pn)
                          ++ map (SI . packageVersion) (lookupPackageName sidx pn)

    buildDeps :: PackageName -> [[Dependency]]
    buildDeps pn = map snd
                 . sortBy (compare `on` fst)
                 $ ((map (\p -> (packageVersion (packageDescription p),
                              maybe []
                                    ( PD.targetBuildDepends
                                    . PD.libBuildInfo
                                    . PD.condTreeData )
                                    (PD.condLibrary $ packageDescription p)) )
                 . lookupPackageName sidx $ pn)
                ++ map (\(v,p) ->
                         (v, concatMap (mapMaybe installedIdtoDep . depends) p)
                       ) (PI.lookupPackageName iidx pn) )

    depdfs :: S.Set PackageName -> [PackageName] -> S.Set PackageName
    depdfs visited [] = visited
    depdfs visited (x:xs)
      | x `S.member` visited = depdfs visited xs
      | otherwise            = depdfs (S.insert x visited) (xs ++ childdeps)
      where
        childdeps = concatMap (map depname) (buildDeps x)


toPackageIds :: VersionMappings -> [ResolvedInstance] -> [PackageIdentifier]
toPackageIds vms = mapMaybe toPkgId
  where
    toPkgId (pn,sv) = do
      (_, stv) <- M.lookup pn vms
      ver      <- getVersion <$> M.lookup sv stv
      return $ PackageIdentifier pn ver


prettyPackageId :: PackageIdentifier -> String
prettyPackageId pkgid =
  (unPackageName $ pkgName pkgid) ++ "-" ++
  (intercalate "." . map show . versionBranch . pkgVersion $ pkgid)


constraintPkgName :: PackageConstraint -> PackageName
constraintPkgName (PackageConstraintVersion   pn _) = pn
constraintPkgName (PackageConstraintInstalled pn  ) = pn
constraintPkgName (PackageConstraintSource    pn  ) = pn
constraintPkgName (PackageConstraintFlags     pn _) = pn
constraintPkgName (PackageConstraintStanzas   pn _) = pn


installedIdtoDep :: InstalledPackageId -> Maybe Dependency
installedIdtoDep (InstalledPackageId pid) = case parts of
  (_:v:xs) -> Just $ Dependency
                      (PackageName . intercalate "-" . reverse $ xs)
                      (ThisVersion . fst . last . readP_to_S parseVersion $ v)
  _        -> Nothing
  where parts = reverse $ splitOn "-" pid
  