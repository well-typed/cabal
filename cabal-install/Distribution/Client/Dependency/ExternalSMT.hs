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

    FlaggedDep(..),
    flaggedDeps,

    depToSConstraint,
    pkgConstraintToSConstraint,

    externalSMTResolver,

    toPackageIds,
    prettyPackageId,

    constraintPkgName,
    installedIdtoDep
  ) where

import Control.Applicative
import Data.Functor

import Distribution.Client.Dependency.Modular.Solver
  ( SolverConfig(..) )
import Distribution.Client.Dependency.Types
  ( DependencyResolver, Progress(..), PackageConstraint(..) )
import Distribution.System
  ( Platform(..) )
import Distribution.Client.Types
  ( SourcePackage(..), InstalledPackage(..) )
import qualified Distribution.PackageDescription as PD
import qualified Distribution.Simple.PackageIndex as PI
import qualified Distribution.Client.ComponentDeps as CD
import Distribution.Client.InstallPlan
  ( PlanPackage(..), ConfiguredPackage(..) )
import Distribution.InstalledPackageInfo
  ( InstalledPackageInfo_(..) )
import Distribution.Package
  ( PackageName(..),
    Dependency(..),
    PackageIdentifier(..),
    InstalledPackageId(..),
    packageVersion )
import Distribution.Client.PackageIndex
  ( PackageIndex,
    lookupPackageName,
    lookupPackageId )
import Distribution.System (OS, Arch)
import Distribution.Compiler
  ( CompilerInfo(..),
    CompilerId(..) )
import Distribution.Version

import Data.Version ( parseVersion )

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe
import Data.List
import Data.List.Split
import Text.ParserCombinators.ReadP (readP_to_S)
import Data.Function (on)
import System.Directory (getHomeDirectory)
import System.FilePath ((</>))

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
  spkgNumInstances    :: SWord32,
  spkgFDeps           :: [([PD.FlagName],[FlaggedDep])],
  spkgSVersion        :: SVersion,
  spkgsSFlags         :: [SBool]
}


type VersionSymbolMap = M.Map InstanceVersion SVersion

type SymbolVersionMap = M.Map Word32 InstanceVersion

-- | For each package, contains maps relating Cabal versions
-- and SMT solver versions to each other.
type VersionMappings  = M.Map PackageName (VersionSymbolMap, SymbolVersionMap)


data InstanceVersion = SI Version
                     | II Version InstalledPackageId
                     deriving (Show, Eq)

instance Ord InstanceVersion where
  (SI x) `compare` (SI y) = x `compare` y
  (II x iidx) `compare` (II y iidy)
    | x == y    = iidx `compare` iidy
    | otherwise = x `compare` y
  (SI x) `compare` (II y _)
    | x == y    = LT
    | otherwise = x `compare` y
  (II x _) `compare` (SI y)
    | x == y    = GT
    | otherwise = x `compare` y

getVersion :: InstanceVersion -> Version
getVersion (SI v  ) = v
getVersion (II v _) = v

isSourceInstance :: InstanceVersion -> Bool
isSourceInstance (SI _) = True
isSourceInstance _      = False

isInstalledInstance :: InstanceVersion -> Bool
isInstalledInstance (II _ _) = True
isInstalledInstance _        = False


data FlaggedDep = Simple Dependency
                | Flagged PD.FlagName [FlaggedDep] [FlaggedDep]
                deriving (Eq, Show)

flaggedDeps :: OS
            -> Arch
            -> CompilerInfo
            -> PD.CondTree PD.ConfVar [Dependency] PD.Library
            -> [FlaggedDep]
flaggedDeps os arch cinfo (PD.CondNode _ deps comps) =
  map Simple deps ++ concatMap branchDeps comps
  where
    branchDeps (c, t, mf) = go c (flaggedDeps os arch cinfo t)
                                 (maybe [] (flaggedDeps os arch cinfo) mf)
    go (PD.Lit True) t _  = t
    go (PD.Lit False) _ f = f
    go (PD.CNot c)    t f = go c f t
    go (PD.CAnd c d)  t f = go c (go d t f) f
    go (PD.COr  c d)  t f = go c t (go d t f)
    go (PD.Var (PD.OS os')) t f
      | os == os' = t
      | otherwise = f
    go (PD.Var (PD.Arch arch'))  t f
      | arch == arch' = t
      | otherwise     = f
    go (PD.Var (PD.Flag fn))     t f = [Flagged fn t f]
    go (PD.Var (PD.Impl cf cvr)) t f
      | matchImpl (compilerInfoId cinfo) ||
        any matchImpl (fromMaybe [] $ compilerInfoCompat cinfo) = t
      | otherwise     = f
      where matchImpl (CompilerId cf' cv) = cf == cf' && withinRange cv cvr


depToSConstraint :: VersionMappings -> Dependency -> SConstraint
depToSConstraint vms (Dependency pn vr) = mkConstraint vr
  where
    mkConstraint (UnionVersionRanges vr1 vr2) =
      \s -> mkConstraint vr1 s ||| mkConstraint vr2 s
    mkConstraint (IntersectVersionRanges vr1 vr2) =
      \s -> mkConstraint vr1 s &&& mkConstraint vr2 s
    mkConstraint (VersionRangeParens vr) = mkConstraint vr
    mkConstraint AnyVersion = (./= 0)
    mkConstraint vr =
      let vs = map snd
             $ filter ((`withinRange` vr) . getVersion . fst) (M.toList vts)
      in if null vs
         then const false
         else \s -> s .>= head vs &&& s .<= last vs

    (vts, _) = fromMaybe (error "ExternalSMT.depToSConstraint: version maps lookup failed")
             $ M.lookup pn vms


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
validateModel :: S.Set PackageName
              -> VersionMappings
              -> [(PackageName,SConstraint)]
              -> M.Map PackageName SPackage
              -> SBool
validateModel targets vms pcs spkgs = bAll checkPkgConstraint pcs
                                  &&& bAll checkPkg (M.toList spkgs)
  where
    checkPkgConstraint :: (PackageName, SConstraint) -> SBool
    checkPkgConstraint (pn, c) = c . spkgSVersion
                               . fromMaybe (error "ExternalSMT.validateModel: lookup failed in checkPkgConstraint")
                               $ M.lookup pn spkgs

    checkPkg :: (PackageName, SPackage) -> SBool
    checkPkg (pn, spkg@(SPackage _ _ ver _))
      | pn `S.member` targets = ver ./= 0 &&& validPkg pn spkg
      | otherwise             = ver .== 0 ||| validPkg pn spkg

    validPkg :: PackageName -> SPackage -> SBool
    validPkg pn (SPackage ni fdeps ver sflags) =
      checkVersionRange ni ver &&& checkDepConstraints pn ver fdeps sflags

    checkVersionRange :: SWord32 -> SVersion -> SBool
    checkVersionRange ni ver = ver .>= 0 &&& ver .<= ni

    checkDepConstraints :: PackageName -> SVersion -> [([PD.FlagName], [FlaggedDep])] -> [SBool] -> SBool
    checkDepConstraints pn ver fdeps sflags =
      bAny (\(v, (fns,fdeps')) -> (v .== ver &&&) . checkAllDeps fdeps'
                                . M.fromList $ zip fns sflags )
           (zip [1..] fdeps)

    checkAllDeps :: [FlaggedDep] -> M.Map PD.FlagName SBool -> SBool
    checkAllDeps fdeps sflags = bAll (checkDependency sflags) fdeps

    checkDependency :: M.Map PD.FlagName SBool -> FlaggedDep -> SBool
    checkDependency _ (Simple d@(Dependency pn _)) =
      maybe false
            (\(SPackage _ _ v _) -> v ./= 0 &&& depToSConstraint vms d v)
            (M.lookup pn spkgs)
    checkDependency sflags (Flagged fn t f) =
      ite ( fromMaybe (error "ExternalSMT.validateModel: lookup failed in checkDependency")
            $ M.lookup fn sflags )
          (checkAllDeps t sflags) (checkAllDeps f sflags)

unFlagName :: PD.FlagName -> String
unFlagName (PD.FlagName f) = f

-- | Create a number of existential variables based on the given list of names.
mkExistentials :: SymWord a => [String] -> Symbolic [SBV a]
mkExistentials = mapM exists


solveSMT :: S.Set PackageName
         -> VersionMappings
         -> [PackageName]
         -> [SWord32]
         -> [(PackageName,SConstraint)]
         -> [[([PD.FlagName],[FlaggedDep])]]
         -> IO (Maybe ([ResolvedInstance], [[Bool]]) )
solveSMT targets vms pns nis pcs fdeps = do
  home  <- getHomeDirectory
  model <- getModel <$> satWith (cfg home) symbolicModel
  case model of
    Right (_, (sln, bs)) -> return $ Just (zip pns sln, groupByCounts flagCounts bs)
    Left  m              -> return Nothing
  --model <- maximize Quantified sum (length pns) (valid targets . mkSPkgs)
  --return $ maybe [] (zip pns) model
  where
    mkSPkgs :: [SVersion] -> [[SBool]] -> M.Map PackageName SPackage
    mkSPkgs svers sflags = M.fromList . zip pns
                         $ zipWith4 SPackage nis fdeps svers sflags

    cfg home = z3 { smtFile = Just $ home </> "smtoutput", timing = True }

    maxFlags :: [([PD.FlagName],[FlaggedDep])] -> Int
    maxFlags fdeps'
      | null fdeps' = 0
      | otherwise   = maximum $ map (length . fst) fdeps'

    flagCounts :: [Int]
    flagCounts = map maxFlags fdeps

    groupByCounts :: [Int] -> [a] -> [[a]]
    groupByCounts [] _ = []
    groupByCounts _ [] = []
    groupByCounts (n:ns) as = let (as', rest) = splitAt n as in
                              as' : groupByCounts ns rest

    symbolicModel :: Symbolic SBool
    symbolicModel = do
      svers  <- mkExistentials (map unPackageName pns)
      sflags <- mapM mkExistVars flagCounts
      return $ validateModel targets vms pcs (mkSPkgs svers sflags)



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
externalSMTResolver :: SolverConfig -> DependencyResolver
externalSMTResolver sc (Platform arch os) cinfo iidx sidx pprefs pcs pns = do
  sln <- solveSMT (S.fromList pns) vms candidatePackages nis pcs' fdeps
  case sln of
    Just (sln', flags) -> return $ Done (mkInstallPlan iidx sidx sln' flags vms)
    Nothing            -> return $ Fail "could not satisfy dependencies"
  where
    nis :: [SWord32]
    nis = map (fromIntegral . M.size . fst) (M.elems vms)

    pcs' :: [(PackageName,SConstraint)]
    pcs' = map (\c -> (constraintPkgName c, pkgConstraintToSConstraint vms c)) pcs

    fdeps :: [[([PD.FlagName],[FlaggedDep])]]
    fdeps = map buildDeps candidatePackages

    vms :: VersionMappings
    vms = M.fromList
        $ zip candidatePackages
        $ map (mkVersionMaps . pkgInstances) candidatePackages

    candidatePackages :: [PackageName]
    candidatePackages = S.toList $ depdfs S.empty pns

    mkVersionMaps :: [InstanceVersion] -> (VersionSymbolMap, SymbolVersionMap)
    mkVersionMaps vs = (M.fromList $ zip vs [1..], M.fromList $ zip [1..] vs)

    pkgInstances :: PackageName -> [InstanceVersion]
    pkgInstances pn = sort $ installedInstances ++ sourceInstances
      where
        installedInstances =
          concatMap (\(v,pkgs) -> map (\p -> II v (installedPackageId p)) pkgs)
                    (PI.lookupPackageName iidx pn)
        sourceInstances = map (SI . packageVersion) (lookupPackageName sidx pn)

    -- TODO: handle installed dependencies correctly. Requires more than just
    --       converting them to Dependency (create intermediate data type?)
    buildDeps :: PackageName -> [([PD.FlagName],[FlaggedDep])]
    buildDeps pn = map snd . sortBy (compare `on` fst)
                 $ sourceDeps ++ installedDeps
      where
        sourceDeps =
          map (\p -> let pd = packageDescription p in
                     (packageVersion pd,
                       (map PD.flagName $ PD.genPackageFlags pd,
                        maybe []
                              (flaggedDeps os arch cinfo)
                              (PD.condLibrary pd))
                     )
              ) (lookupPackageName sidx pn)
        installedDeps =
          map (\(v,p) ->
                (v, ([], concatMap (map Simple . mapMaybe installedIdtoDep . depends) p))
              ) (PI.lookupPackageName iidx pn) 

    depdfs :: S.Set PackageName -> [PackageName] -> S.Set PackageName
    depdfs visited [] = visited
    depdfs visited (x:xs)
      | x `S.member` visited = depdfs visited xs
      | otherwise            = depdfs (S.insert x visited) (xs ++ childdeps)
      where
        childdeps = concatMap (concatMap fdepnames . snd) (buildDeps x)
        fdepnames (Simple (Dependency pn _)) = [pn]
        fdepnames (Flagged _ t f           ) = concatMap fdepnames (t ++ f)


mkInstallPlan :: PI.InstalledPackageIndex
              -> PackageIndex SourcePackage
              -> [ResolvedInstance]
              -> [[Bool]]
              -> VersionMappings
              -> [PlanPackage]
mkInstallPlan iidx sidx ris flagVals vms = catMaybes
                                         $ zipWith mkPlanPackage ris flagVals
  where
    mkPlanPackage (pn, v) flagVals' = do
      (_,stv)   <- M.lookup pn vms
      pInstance <- M.lookup v stv
      case pInstance of
        II ver instId -> do p <- PI.lookupInstalledPackageId iidx instId
                            return $ PreExisting (InstalledPackage p [])
        SI ver        -> do p <- lookupPackageId sidx (PackageIdentifier pn ver)
                            return $ Configured $ ConfiguredPackage
                              p 
                              (zip (map PD.flagName . PD.genPackageFlags
                                    . packageDescription $ p) flagVals')
                              []
                              (CD.fromList [])


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
                      (thisVersion . fst . last . readP_to_S parseVersion $ v)
  _        -> Nothing
  where parts = reverse $ splitOn "-" pid
