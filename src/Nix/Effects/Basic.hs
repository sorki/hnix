{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}

{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Nix.Effects.Basic where

import           Control.Monad.Writer
import           Control.Arrow

import           Control.Monad
import           Control.Monad.State.Strict
import           Data.Char                      ( isAscii, isAlphaNum )
import           Data.Foldable                  ( foldrM )
import           Data.HashMap.Lazy              ( HashMap )
import qualified Data.HashMap.Lazy             as M
import           Data.List
import           Data.List.Split
import           Data.Maybe                     ( maybeToList )
import qualified Data.HashSet                  as S
import           Data.Text                      ( Text )
import qualified Data.Text                     as Text
import           Data.Text.Prettyprint.Doc
import           Nix.Atoms
import           Nix.Convert
import           Nix.Effects
import           Nix.Exec                       ( MonadNix
                                                , callFunc
                                                , evalExprLoc
                                                , nixInstantiateExpr
                                                , fromStringNoContext
                                                )
import           Nix.Expr
import           Nix.Frames
import           Nix.Json                       ( nvalueToJSONNixString )
import           Nix.Normal
import           Nix.Parser
import           Nix.Pretty
import           Nix.Render
import           Nix.Scope
import           Nix.String
import           Nix.String.Coerce
import           Nix.Utils
import           Nix.Value
import           Nix.Value.Monad
import           System.FilePath

#ifdef MIN_VERSION_ghc_datasize
#if MIN_VERSION_ghc_datasize(0,2,0)
import           GHC.DataSize
#endif
#endif

defaultMakeAbsolutePath :: MonadNix e t f m => FilePath -> m FilePath
defaultMakeAbsolutePath origPath = do
  origPathExpanded <- expandHomePath origPath
  absPath          <- if isAbsolute origPathExpanded
    then pure origPathExpanded
    else do
      cwd <- do
        mres <- lookupVar "__cur_file"
        case mres of
          Nothing -> getCurrentDirectory
          Just v  -> demand v $ \case
            NVPath s -> return $ takeDirectory s
            v ->
              throwError
                $  ErrorCall
                $  "when resolving relative path,"
                ++ " __cur_file is in scope,"
                ++ " but is not a path; it is: "
                ++ show v
      pure $ cwd <///> origPathExpanded
  removeDotDotIndirections <$> canonicalizePath absPath

expandHomePath :: MonadFile m => FilePath -> m FilePath
expandHomePath ('~' : xs) = flip (++) xs <$> getHomeDirectory
expandHomePath p          = return p

-- | Incorrectly normalize paths by rewriting patterns like @a/b/..@ to @a@.
--   This is incorrect on POSIX systems, because if @b@ is a symlink, its
--   parent may be a different directory from @a@. See the discussion at
--   https://hackage.haskell.org/package/directory-1.3.1.5/docs/System-Directory.html#v:canonicalizePath
removeDotDotIndirections :: FilePath -> FilePath
removeDotDotIndirections = intercalate "/" . go [] . splitOn "/"
 where
  go s       []            = reverse s
  go (_ : s) (".." : rest) = go s rest
  go s       (this : rest) = go (this : s) rest

infixr 9 <///>
(<///>) :: FilePath -> FilePath -> FilePath
x <///> y | isAbsolute y || "." `isPrefixOf` y = x </> y
          | otherwise                          = joinByLargestOverlap x y
 where
  joinByLargestOverlap (splitDirectories -> xs) (splitDirectories -> ys) =
    joinPath $ head
      [ xs ++ drop (length tx) ys | tx <- tails xs, tx `elem` inits ys ]

defaultFindEnvPath :: MonadNix e t f m => String -> m FilePath
defaultFindEnvPath = findEnvPathM

findEnvPathM :: forall e t f m . MonadNix e t f m => FilePath -> m FilePath
findEnvPathM name = do
  mres <- lookupVar "__nixPath"
  case mres of
    Nothing -> error "impossible"
    Just x  -> demand x $ fromValue >=> \(l :: [NValue t f m]) ->
      findPathBy nixFilePath l name
 where
  nixFilePath :: MonadEffects t f m => FilePath -> m (Maybe FilePath)
  nixFilePath path = do
    path   <- makeAbsolutePath @t @f path
    exists <- doesDirectoryExist path
    path'  <- if exists
      then makeAbsolutePath @t @f $ path </> "default.nix"
      else return path
    exists <- doesFileExist path'
    return $ if exists then Just path' else Nothing

findPathBy
  :: forall e t f m
   . MonadNix e t f m
  => (FilePath -> m (Maybe FilePath))
  -> [NValue t f m]
  -> FilePath
  -> m FilePath
findPathBy finder l name = do
  mpath <- foldM go Nothing l
  case mpath of
    Nothing ->
      throwError
        $  ErrorCall
        $  "file '"
        ++ name
        ++ "' was not found in the Nix search path"
        ++ " (add it's using $NIX_PATH or -I)"
    Just path -> return path
 where
  go :: Maybe FilePath -> NValue t f m -> m (Maybe FilePath)
  go p@(Just _) _ = pure p
  go Nothing l =
    demand l $ fromValue >=> \(s :: HashMap Text (NValue t f m)) -> do
      p <- resolvePath s
      demand p $ fromValue >=> \(Path path) -> case M.lookup "prefix" s of
        Nothing -> tryPath path Nothing
        Just pf -> demand pf $ fromValueMay >=> \case
          Just (nsPfx :: NixString) ->
            let pfx = hackyStringIgnoreContext nsPfx
            in  if not (Text.null pfx)
                  then tryPath path (Just (Text.unpack pfx))
                  else tryPath path Nothing
          _ -> tryPath path Nothing

  tryPath p (Just n) | n' : ns <- splitDirectories name, n == n' =
    finder $ p <///> joinPath ns
  tryPath p _ = finder $ p <///> name

  resolvePath s = case M.lookup "path" s of
    Just t  -> return t
    Nothing -> case M.lookup "uri" s of
      Just ut -> defer $ fetchTarball ut
      Nothing ->
        throwError
          $  ErrorCall
          $  "__nixPath must be a list of attr sets"
          ++ " with 'path' elements, but received: "
          ++ show s

fetchTarball
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
fetchTarball = flip demand $ \case
  NVSet s _ -> case M.lookup "url" s of
    Nothing ->
      throwError $ ErrorCall "builtins.fetchTarball: Missing url attribute"
    Just url -> demand url $ go (M.lookup "sha256" s)
  v@NVStr{} -> go Nothing v
  v ->
    throwError
      $  ErrorCall
      $  "builtins.fetchTarball: Expected URI or set, got "
      ++ show v
 where
  go :: Maybe (NValue t f m) -> NValue t f m -> m (NValue t f m)
  go msha = \case
    NVStr ns -> fetch (hackyStringIgnoreContext ns) msha
    v ->
      throwError
        $  ErrorCall
        $  "builtins.fetchTarball: Expected URI or string, got "
        ++ show v

{- jww (2018-04-11): This should be written using pipes in another module
    fetch :: Text -> Maybe (NThunk m) -> m (NValue t f m)
    fetch uri msha = case takeExtension (Text.unpack uri) of
        ".tgz" -> undefined
        ".gz"  -> undefined
        ".bz2" -> undefined
        ".xz"  -> undefined
        ".tar" -> undefined
        ext -> throwError $ ErrorCall $ "builtins.fetchTarball: Unsupported extension '"
                  ++ ext ++ "'"
-}

  fetch :: Text -> Maybe (NValue t f m) -> m (NValue t f m)
  fetch uri Nothing =
    nixInstantiateExpr $ "builtins.fetchTarball \"" ++ Text.unpack uri ++ "\""
  fetch url (Just t) = demand t $ fromValue >=> \nsSha ->
    let sha = hackyStringIgnoreContext nsSha
    in  nixInstantiateExpr
          $  "builtins.fetchTarball { "
          ++ "url    = \""
          ++ Text.unpack url
          ++ "\"; "
          ++ "sha256 = \""
          ++ Text.unpack sha
          ++ "\"; }"

defaultFindPath :: MonadNix e t f m => [NValue t f m] -> FilePath -> m FilePath
defaultFindPath = findPathM

findPathM
  :: forall e t f m
   . MonadNix e t f m
  => [NValue t f m]
  -> FilePath
  -> m FilePath
findPathM = findPathBy path
 where
  path :: MonadEffects t f m => FilePath -> m (Maybe FilePath)
  path path = do
    path   <- makeAbsolutePath @t @f path
    exists <- doesPathExist path
    return $ if exists then Just path else Nothing

defaultImportPath
  :: (MonadNix e t f m, MonadState (HashMap FilePath NExprLoc) m)
  => FilePath
  -> m (NValue t f m)
defaultImportPath path = do
  traceM $ "Importing file " ++ path
  withFrame Info (ErrorCall $ "While importing file " ++ show path) $ do
    imports <- get
    evalExprLoc =<< case M.lookup path imports of
      Just expr -> pure expr
      Nothing   -> do
        eres <- parseNixFileLoc path
        case eres of
          Failure err ->
            throwError
              $ ErrorCall
              . show $ fillSep ["Parse during import failed:", err]
          Success expr -> do
            modify (M.insert path expr)
            pure expr

defaultPathToDefaultNix :: MonadNix e t f m => FilePath -> m FilePath
defaultPathToDefaultNix = pathToDefaultNixFile

-- Given a path, determine the nix file to load
pathToDefaultNixFile :: MonadFile m => FilePath -> m FilePath
pathToDefaultNixFile p = do
  isDir <- doesDirectoryExist p
  pure $ if isDir then p </> "default.nix" else p

defaultDerivationStrict
  :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
defaultDerivationStrict = fromValue @(AttrSet (NValue t f m)) >=> \s -> do
  nn <- maybe (pure False) (demand ?? fromValue) (M.lookup "__ignoreNulls" s)
  s' <- M.fromList <$> mapMaybeM (handleEntry nn) (M.toList s)
  v' <- normalForm =<< toValue @(AttrSet (NValue t f m)) @_ @(NValue t f m) s'
  nixInstantiateExpr $ "derivationStrict " ++ show (prettyNValue v')
 where
  mapMaybeM :: (a -> m (Maybe b)) -> [a] -> m [b]
  mapMaybeM op = foldr f (return [])
    where f x xs = op x >>= (<$> xs) . (++) . maybeToList

  handleEntry :: Bool -> (Text, NValue t f m) -> m (Maybe (Text, NValue t f m))
  handleEntry ignoreNulls (k, v) = fmap (k, ) <$> case k of
      -- The `args' attribute is special: it supplies the command-line
      -- arguments to the builder.
      -- TODO This use of coerceToString is probably not right and may
      -- not have the right arguments.
    "args"          -> demand v $ fmap Just . coerceNixList
    "__ignoreNulls" -> pure Nothing
    _               -> demand v $ \case
      NVConstant NNull | ignoreNulls -> pure Nothing
      v'                             -> Just <$> coerceNix v'
   where
    coerceNix :: NValue t f m -> m (NValue t f m)
    coerceNix = toValue <=< coerceToString callFunc CopyToStore CoerceAny

    coerceNixList :: NValue t f m -> m (NValue t f m)
    coerceNixList v = do
      xs <- fromValue @[NValue t f m] v
      ys <- traverse (`demand` coerceNix) xs
      toValue @[NValue t f m] ys

data HashType = SHA256 | MD5 | SHA1

data Derivation = Derivation
  { name :: Text
  , outputNames :: [ Text ]
  , outputs :: M.HashMap Text Text
  , inputs :: S.HashSet StringContext
  , platform :: Text
  , builder :: Text -- should be typed as a store path
  , args :: [ Text ]
  , env :: M.HashMap Text Text
  , mFixed :: Maybe (Text, HashType)
  , hashMode :: HashMode
  , useJson :: Bool
  }

data HashMode = Flat | Recursive


defaultDerivationStrict' :: forall e t f m . MonadNix e t f m => NValue t f m -> m Derivation -- m (NValue t f m)
defaultDerivationStrict' = fromValue @(AttrSet (NValue t f m)) >=> \s -> do
    (drv@Derivation {..}, ctx) <- runWithStringContextT' $ buildDerivationWithContext s
    drv' <- case mFixed of
      Just (hash, hashType) -> do
        outPath <- makeFixedOutputPath (hashMode == Recursive) (Digest @hashType hash) name (toStorePaths ctx)
        let env' = M.insert "out" outPath env
        return $ drv { env = env', outputs = M.singleton "out" outPath }
      Nothing -> do
        hash <- hashDerivationModulo (drv 
                    { inputs = ctx
                    , env = if useJson then env else foldl' (flip M.insert "") outputNames env
                    })
        return $ drv 
            { env = if useJson then env else M.insertFromList (map (\o -> makeOutputPath o hash name) outputs) env
            , inputs = ctx
            , outputs = M.fromList $ map (\o -> makeOutputPath o hash name) outputs
            }

    drvPath <- writeDerivation drv

    return $ flip nvSet M.empty $ M.insert "drvPath" drvPath (outputs drv')
        
  where
    

    -- | Build a derivation in a context collecting dependencies.
    -- This is complex from a typing standpoint, but it allows to perform the
    -- full computation without worrying too much about all the string's contexts.
    buildDerivationWithContext :: (MonadNix e t f m) => AttrSet (NValue t f m) -> WithStringContextT m Derivation
    buildDerivationWithContext s = do
        -- Parse name first, so we can add an informative frame
        drvName     <- getAttr      "name"              $ extractNixString >=> assertDrvStoreName
        withFrame' Info (ErrorCall $ "While evaluating derivation " ++ show drvName) $ do

          useJson     <- getAttrOr    "__structuredAttrs" (return False)   $ return
          ignoreNulls <- getAttrOr    "__ignoreNulls"     (return False)   $ return

          args        <- getAttr      "args"              $ mapM (fromValue' >=> extractNixString)
          builder     <- getAttr      "builder"           $ extractNixString
          platform    <- getAttr      "system"            $ extractNoCtx >=> assertNonNull
          mHash       <- getAttrOr    "outputHash"        (return Nothing) $ extractNoCtx >=> (return . Just)
          hashMode    <- getAttrOr    "outputHashMode"    (return Flat)    $ extractNoCtx >=> parseHashMode
          outputs     <- getAttrOr    "outputs"           (return ["out"]) $ mapM (fromValue' >=> extractNoCtx)

          mFixedOutput <- case mHash of
            Nothing -> return Nothing
            Just hash -> do
              when (outputs /= ["out"]) $ lift $ throwError $ ErrorCall $ "Multiple outputs are not supported for fixed-output derivations"
              hashType <- getAttr "outputHashAlgo" $ extractNoCtx >=> parseHashType
              return $ Just (hash, hashType)

          -- filter out null values if needed.
          attrs <- if not ignoreNulls
            then return s
            else M.mapMaybe id <$> forM s (demand' ?? (\case
                NVConstant NNull -> return Nothing
                value -> return $ Just value
              ))

          env <- if useJson
            then do
              jsonString :: NixString <- lift $ nvalueToJSONNixString $ flip nvSet M.empty $ 
                deleteAll [ "args", "__ignoreNulls", "__structuredAttrs" ] attrs
              string :: Text <- extractNixString jsonString
              return $ M.singleton "__json" string
            else
              mapM (lift . coerceToString callFunc CopyToStore CoerceAny >=> extractNixString) $
                deleteAll [ "args", "__ignoreNulls" ] attrs

          return $ Derivation drvName outputs M.empty S.empty platform builder args env mFixedOutput hashMode useJson
      where 
        -- common functions, lifted to WithStringContextT

        demand' :: NValue t f m -> (NValue t f m -> WithStringContextT m a) -> WithStringContextT m a
        demand' v f = join $ lift $ demand v (return . f)

        -- (FromValue a m (NValue t f m)) would also make sense, but triggers -Wsimplifiable-class-constraints
        fromValue' :: (FromValue a m (NValue' t f m (NValue t f m)), MonadNix e t f m) => NValue t f m -> WithStringContextT m a
        fromValue' = lift . fromValue

        withFrame' :: (Framed e m, Exception s) => NixLevel -> s -> WithStringContextT m a -> WithStringContextT m a
        withFrame' level f = join . lift . withFrame level f . return

        -- shortcuts to `forceValue'` an AttrSet field

        getAttrOr :: (MonadNix e t f m, FromValue v m (NValue' t f m (NValue t f m)))
          => Text -> WithStringContextT m a -> (v -> WithStringContextT m a) -> WithStringContextT m a
        getAttrOr n d f = flip (maybe d) (M.lookup n s) $ \v ->  
          withFrame' Info (ErrorCall $ "While evaluating attribute '" ++ show n ++ "'") $ fromValue' v >>= f

        getAttr n = getAttrOr n (lift $ throwError $ ErrorCall $ "Required attribute '" ++ show n ++ "' not found.")

        -- Test validity for fields

        assertDrvStoreName :: MonadNix e t f m => Text -> WithStringContextT m Text
        assertDrvStoreName name = lift $ do
          let invalid c = not $ isAscii c && (isAlphaNum c || c `elem` ("+-._?=" :: String)) -- isAlphaNum allows non-ascii chars.
          let fail reason = throwError $ ErrorCall $ "Store name " ++ show name ++ " " ++ reason
          when ("." `Text.isPrefixOf` name)    $ fail "cannot start with a period"
          when (Text.length name > 211)        $ fail "must be no longer than 211 characters"
          when (Text.any invalid name)         $ fail "contains some invalid character"
          when (".drv" `Text.isSuffixOf` name) $ fail "is not allowed to end in '.drv'"
          return name

        extractNoCtx :: MonadNix e t f m => NixString -> WithStringContextT m Text
        extractNoCtx ns = case principledGetStringNoContext ns of
          Nothing -> lift $ throwError $ ErrorCall $ "The string " ++ show ns ++ " is not allowed to have a context."
          Just v -> return v

        assertNonNull :: MonadNix e t f m => Text -> WithStringContextT m Text
        assertNonNull t = do
          when (Text.null t) $ lift $ throwError $ ErrorCall "Value must not be empty"
          return t

        parseHashMode :: MonadNix e t f m => Text -> WithStringContextT m HashMode
        parseHashMode = \case 
          "flat" ->      return Flat
          "recursive" -> return Recursive
          other -> lift $ throwError $ ErrorCall $ "Hash mode " ++ show other ++ " is not valid. It must be either 'flat' or 'recursive'"

        parseHashType :: Text -> WithStringContextT m HashType
        parseHashType = \case
          "sha1"   -> return SHA1
          "sha256" -> return SHA256
          "md5"    -> return MD5
          other -> lift $ throwError $ ErrorCall $ "Hash type " ++ show other ++ " is not a valid hash type"

        -- Other helpers

        deleteAll :: [Text] -> AttrSet a -> AttrSet a
        deleteAll keys s = foldl' (flip M.delete) s keys


defaultTraceEffect :: MonadPutStr m => String -> m ()
defaultTraceEffect = Nix.Effects.putStrLn
