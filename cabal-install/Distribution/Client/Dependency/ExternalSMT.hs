module Distribution.Client.Dependency.ExternalSMT
  ( SVersion,
    SConstraint,
    SDepConstraints,
    SPackage(..),

    VersionSymbolMap,
    SymbolVersionMap,
    VersionMappings,

    ResolvedInstance,

    mkSymConstraint,

    externalSMTResolver
  ) where


import Distribution.Client.Dependency.Modular.Solver
  ( SolverConfig(..) )
import Distribution.Client.Dependency.Types
  ( DependencyResolver, Progress(..) )
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
import Distribution.Package
    ( PackageName(..),
      Dependency(..),
      PackageIdentifier(..),
      packageVersion )
import Distribution.Client.PackageIndex
  ( lookupPackageName )
import Distribution.Version

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe, fromJust)
import Data.List
import Data.Function (on)

import Data.SBV

import Debug.Trace (trace)
import System.IO.Unsafe (unsafePerformIO)


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
  spkgSDepConstraints :: [SDepConstraints],
  spkgSVersion        :: SVersion
}


type VersionSymbolMap = M.Map Version SVersion
type SymbolVersionMap = M.Map Word32 Version
type VersionMappings  = M.Map PackageName (VersionSymbolMap, SymbolVersionMap)


mkSymConstraint :: VersionMappings -> Dependency -> SConstraint
mkSymConstraint vms (Dependency pn vr) = mkConstraint vr
  where
    -- TODO: clean up
    mkConstraint AnyVersion             = const true
    mkConstraint (ThisVersion v)        =
      maybe (const false) (.==) (M.lookup v vts)
    mkConstraint (LaterVersion v)       =
      let xs = dropWhile ((<= v) . fst) $ M.toList vts
      in if null xs
         then const false
         else \s -> s .> (snd $ head xs)
    mkConstraint (EarlierVersion v)     =
      let xs = dropWhile ((<= v) . fst) $ M.toList vts
      in if null xs
         then const false
         else \s -> s .< (snd $ head xs)
    mkConstraint vr'@(WildcardVersion _) =
      let xs = takeWhile ((\v -> withinRange v vr') . fst)
             . dropWhile ((not . (\v -> withinRange v vr')) . fst)
             $ M.toList vts
      in if null xs 
         then const false
         else \s -> s .>= (snd $ head xs) &&& s .<= (snd $ last xs)
    mkConstraint (UnionVersionRanges vr1 vr2) =
      \s -> mkConstraint vr1 s ||| mkConstraint vr2 s
    mkConstraint (IntersectVersionRanges vr1 vr2) =
      \s -> mkConstraint vr1 s &&& mkConstraint vr2 s
    mkConstraint (VersionRangeParens vr') = mkConstraint vr'

    -- TODO: fix fromJust
    (vts, _) = fromJust $ M.lookup pn vms


-- | validate an install plan model
valid :: S.Set PackageName -> [SPackage] -> SBool
valid targets spkgs = bAll checkPkg spkgs
  where
    checkPkg (SPackage pn ni _ ver)
      | pn `S.member` targets = ver ./= 0
                            &&& rangeFine ni ver
                            &&& checkConstraints pn ver
      | otherwise             = rangeFine ni ver
                            &&& checkConstraints pn ver
    rangeFine ni ver = ver .>= 0 &&& ver .<= ni
    checkConstraints pn ver = bAll (checkPkgConstraints pn ver) spkgs
    checkPkgConstraints pn ver (SPackage _ _ dcs ver') =
          ver' .== 0 |||
          bOr (zipWith (\v dcs' -> v .== ver' &&&
                         bAll ($ ver)
                              (fromMaybe [] $ ((./= 0) :) <$> M.lookup pn dcs')
                       ) [1..] dcs)


solveSMT :: S.Set PackageName
         -> [PackageName]
         -> [SWord32]
         -> [[SDepConstraints]]
         -> IO [ResolvedInstance]
solveSMT targets pns nis dcs = do
  model <- getModel <$> sat ( (valid targets . mkSPkgs) <$>
                              mkExistVars (length pns) )
  case model of
    Right (_, sln) -> return $ zip pns sln
    Left  m        -> print m >> return []
  where
    mkSPkgs              = map (uncurry4 SPackage) . zip4 pns nis dcs
    uncurry4 f (a,b,c,d) = f a b c d


-- TODO: - use all package instances, not just source packages
--       - make it adhere to all Cabal flags and constraints
externalSMTResolver :: SolverConfig -> DependencyResolver
externalSMTResolver sc (Platform arch os) cinfo iidx sidx pprefs pcs pns =
  let sln  = unsafePerformIO $ solveSMT (S.fromList pns) allTargets nis dcs
      sln' = toPackageIds vms $ filter ((/= 0) . snd) sln
  in trace (show $ map prettyPackageId sln') $ Fail "not fully implemented yet"
  where
    nis :: [SWord32]
    nis = map (fromIntegral . length . pkgVersions) allTargets

    dcs :: [[SDepConstraints]]
    dcs = map (map (M.fromList . map (\d -> (depname d, [mkSymConstraint vms d]))))
        . map buildDeps $ allTargets

    vms :: VersionMappings
    vms = M.fromList
        $ zip allTargets
        $ map (\pn -> mkVersionMaps (sort $ pkgVersions pn)) allTargets

    allTargets :: [PackageName]
    allTargets = S.toList $ depdfs S.empty pns

    depname (Dependency pkgname _) = pkgname

    mkVersionMaps vs = (M.fromList $ zip vs [1..], M.fromList $ zip [1..] vs)

    pkgs = lookupPackageName sidx

    pkgVersions = map packageVersion . pkgs

    buildDeps :: PackageName -> [[Dependency]]
    buildDeps (PackageName "base") = [[]]
    buildDeps pn  = map (\p -> maybe []
                                     ( PD.targetBuildDepends
                                     . PD.libBuildInfo
                                     . PD.condTreeData )
                                     (PD.condLibrary $ packageDescription p) )
                  . sortBy (compare `on` packageVersion)
                  . pkgs $ pn

    depdfs :: S.Set PackageName -> [PackageName] -> S.Set PackageName
    depdfs visited [] = visited
    depdfs visited (x:xs)
      | x `S.member` visited = depdfs visited xs
      | otherwise            = depdfs (S.insert x visited) (xs ++ childdeps)
      where
        childdeps = concatMap ( filter ((not) . (`S.member` visited))
                              . (map depname)
                              ) (buildDeps x)


toPackageIds :: VersionMappings -> [ResolvedInstance] -> [PackageIdentifier]
toPackageIds vms ris = map toPkgId ris
  where
    -- TODO: fix this
    toPkgId (pn,sv) = let (_, stv) = fromJust $ M.lookup pn vms
                          ver      = fromJust $ M.lookup sv stv
                      in PackageIdentifier pn ver


prettyPackageId :: PackageIdentifier -> String
prettyPackageId pkgid =
  (unPackageName $ pkgName pkgid) ++ "-" ++
  (intercalate "." . map show . versionBranch . pkgVersion $ pkgid)