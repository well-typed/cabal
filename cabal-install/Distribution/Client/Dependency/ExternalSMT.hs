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


import Control.Applicative ((<$>))
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
import qualified Distribution.Simple.PackageIndex as IPI
import Distribution.InstalledPackageInfo
  ( InstalledPackageInfo_(..) )
import Distribution.Package
    ( PackageName(..),
      Dependency(..),
      PackageIdentifier(..),
      InstalledPackageId(..),
      packageVersion )
import qualified Distribution.Client.PackageIndex as SPI
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

-- | selected package version
type SMTVersion = Word32

-- | resolved package instance
type ResolvedInstance = (PackageName, SMTVersion)

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


-- | Maps Cabal versions to SMT solver versions.
--
-- TODO: I think this should map to SMTVersion rather than SVersion.
type VersionSymbolMap = M.Map InstanceVersion SVersion

-- | Maps SMT solver versions to Cabal versions.
type SymbolVersionMap = M.Map SMTVersion InstanceVersion

-- | For each package, contains maps relating Cabal versions
-- and SMT solver versions to each other.
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


-- | Generates the constraints that describe what constitutes a valid
-- install plan.
valid :: S.Set PackageName   -- ^ the target packages (from the command line)
      -> [SPackage]          -- ^ all relevant packages (contains the variables)
      -> SBool
valid targets spkgs = bAll checkPkg spkgs
  where
    -- Generates the constraints for one individual package.
    --
    -- In particular, if a package is among the targets, then the solver
    -- must choose a version for it (it may choose an installed version).
    checkPkg (SPackage pn ni pcs _ ver)
      | pn `S.member` targets = ver ./= 0 &&& validPkg pn ni pcs ver
      | otherwise             =               validPkg pn ni pcs ver

    -- Further per-package constraints.
    --
    -- For each package, we generate, the following constraints:
    --
    --   * The version must be in the range of the available versions.
    --     If n instances of the package are available, the value of the
    --     package variable must be between 0 (which means ignore) and n.
    --
    --   * If there are input constraints for this package, we'll
    --     generate them. (TODO: I'd prefer to do this in a separate
    --     pass, as these are problem-specific (to the individual solver
    --     invocation), whereas typically the layout of the dependencies
    --     is more global. It's a minor point though.)
    --
    --   * Reflect the dependencies of the package as constraints on
    --     other variables.
    --
    validPkg pn ni pcs ver = rangeFine ni ver
                         &&& checkConstraints ver pcs
                    --     &&& checkDepConstraints pn ver

    -- Checks that a given package instance is in allowed range.
    rangeFine ni ver = ver .>= 0 &&& ver .<= ni
    checkConstraints ver cs = bAll ($ ver) cs
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

-- | This is the entry point for the external SMT solver.
--
-- Its type is dictated by the generic cabal-install solver interface.
-- What we do here is to pre-analyze the data we have available and turn
-- it into the format that is needed so that we can the SMT solver.
--
-- TODO: - flags, stanzas, etc
--
-- TODO: reverse translate the output of the SMT solver into what is
-- actually expected by the rest of cabal-install.
--
-- TODO: The style of this function is suboptimal. We're computing
-- a lot of different lists for solveSMT, namely allTargets, nis,
-- pcs', dcs, only to then zip them together. Why don't we produce
-- a single list in the first place? If we look at nis, pcs' and
-- dcs, then all three are just maps over allTargets. So rather than
-- doing three separate maps over allTargets with a subsequent zip,
-- let's just do a single map over allTargets. I.e., write functions,
-- ideally on the top level, that for a single package compute the
-- number of available instances, the package constraints, and the
-- dependency constraints. Then call SPackage (per package). We can
-- feed the [SVersion -> SPackage] to solveSMT, and everything will
-- be a bit more direct.
--
externalSMTResolver :: SolverConfig -> DependencyResolver
externalSMTResolver sc (Platform arch os) cinfo iidx sidx pprefs pcs pns = do
  sln <- solveSMT (S.fromList pns) allTargets nis pcs' dcs

  -- From the solver, we get a model.
  --
  -- At this point, 'sln' is a mapping from package variable names to
  -- selected versions (using the numbering exposed to the SMT solver).
  --
  -- We have to translate the selected versions back into actual
  -- package instances. The map 'vms' contains the necessary mapping
  -- between Cabal versions and SMT solver versions.
  let sln' = toPackageIds vms sln

  -- For now, we then simply print the selected versions ...
  print $ map prettyPackageId sln'
  -- ... and always fail.
  return $ Fail "not fully implemented yet"
  where

    -- This is the list of all relevant packages.
    --
    -- TODO: This is misnamed. These aren't "targets".
    --
    -- It's computed by traversing the package index and simply including all
    -- packages that could possibly occur as dependencies. The starting point
    -- are the actual targets, i.e., the usually user-specified packages.
    --
    allTargets :: [PackageName]
    allTargets = S.toList $ depdfs S.empty pns

    buildDeps :: PackageName -> [[Dependency]]
    buildDeps pn = map snd
                 . sortBy (compare `on` fst)
                 $ ((map (\p -> (packageVersion (packageDescription p),
                              maybe []
                                    ( PD.targetBuildDepends
                                    . PD.libBuildInfo
                                    . PD.condTreeData )
                                    (PD.condLibrary $ packageDescription p)) )
                 . SPI.lookupPackageName sidx $ pn)
                ++ map (\(v,p) ->
                         (v, concatMap (mapMaybe installedIdtoDep . depends) p)
                       ) (IPI.lookupPackageName iidx pn) )

    depdfs :: S.Set PackageName -> [PackageName] -> S.Set PackageName
    depdfs visited [] = visited
    depdfs visited (x:xs)
      | x `S.member` visited = depdfs visited xs
      | otherwise            = depdfs (S.insert x visited) (xs ++ childdeps)
      where
        childdeps = concatMap (map (\ (Dependency pkgname _) -> pkgname)) (buildDeps x)

    -- For all packages, compute the number of instances that are available.
    --
    -- TODO: Why is this not directly attached to each individual package?
    -- Why does it not reuse the version map?
    nis :: [SWord32]
    nis = map (fromIntegral . length . pkgInstances) allTargets

    -- For a given package name, determines the list of all available
    -- instances, in ascending order. Looks up both installed and source
    -- packages from their respective package indexes.
    pkgInstances :: PackageName -> [InstanceVersion]
    pkgInstances pn = sort $ map (II . fst) (IPI.lookupPackageName iidx pn)
                          ++ map (SI . packageVersion) (SPI.lookupPackageName sidx pn)

    -- Translates the incoming package constraints into symbolic
    -- constraints.
    --
    -- TODO: It's unclear what we do all the grouping for. I think it
    -- is because we do not have the variables available at this point.
    -- But this should be solved differently.
    pcs' :: [[SConstraint]]
    pcs' = map (map (pkgConstraintToSConstraint vms) . groupConstraints)
               allTargets

    -- TODO: Quite inefficient grouping function.
    groupConstraints :: PackageName -> [PackageConstraint]
    groupConstraints pn = filter (\pc -> pn == constraintPkgName pc) pcs

    dcs :: [[SDepConstraints]]
    dcs = map ( map (M.fromList
              . map (\d @ (Dependency pkgname _) -> (pkgname, [depToSConstraint vms d])))
              . buildDeps ) allTargets


    vms :: VersionMappings
    vms = M.fromList
        $ zip allTargets
        $ map (mkVersionMaps . pkgInstances) allTargets

    -- Helper function that creates the actual version associations.
    mkVersionMaps :: [InstanceVersion] -> (VersionSymbolMap, SymbolVersionMap)
    mkVersionMaps vs = (M.fromList $ zip vs [1..], M.fromList $ zip [1..] vs)


pkgInstances :: PackageName -> IPI.InstalledPackageIndex -> SPI.PackageIndex SourcePackage -> [InstanceVersion]
pkgInstances pn iidx sidx = sort $ map (II . fst) (IPI.lookupPackageName iidx pn)
                                ++ map (SI . packageVersion) (SPI.lookupPackageName sidx pn)

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
