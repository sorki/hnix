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
{-# LANGUAGE RecordWildCards #-}

{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}


{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NamedFieldPuns #-}

module Nix.Effects.Basic where


import Prelude hiding (readFile)

import           Control.Monad.Writer
import           Control.Arrow

import           Control.Monad
import           Control.Monad.State.Strict
import           Data.Char                      ( isAscii, isAlphaNum )
import           Data.Either                    ( fromRight )
import           Data.Foldable                  ( foldrM )
import           Data.HashMap.Lazy              ( HashMap )
import qualified Data.HashMap.Lazy             as M
import qualified Data.Map.Strict               as Map
import           Data.Map.Strict                ( Map )
import qualified Data.Set                      as Set
import           Data.Set                       ( Set )
import           Data.List
import           Data.List.Split                ( splitOn )
import           Data.Maybe                     ( maybeToList, fromJust )
import qualified Data.HashSet                  as S
import           Data.Text                      ( Text )
import qualified Data.Text                     as Text
import qualified Data.Text.Encoding            as Text
import           Data.Text.Prettyprint.Doc
import           Data.Traversable               ( for )
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

import qualified System.Nix.ReadonlyStore      as Store
import qualified System.Nix.Hash               as Store
import qualified System.Nix.StorePath          as Store
import qualified System.Nix.Store.Remote       as Store
import qualified System.Nix.Store.Remote.Types as Store
import qualified System.Nix.StorePath          as Store

import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer    as L

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

instance Show HashType where
  show SHA256 = "sha256"
  show MD5 = "md5"
  show SHA1 = "sha1"

data Derivation = Derivation
  { name :: Text
  , outputs :: Map Text Text
  , inputs :: (Set Text, Map Text [Text])
  , platform :: Text
  , builder :: Text -- should be typed as a store path
  , args :: [ Text ]
  , env :: Map Text Text
  , mFixed :: Maybe Store.SomeNamedDigest
  , hashMode :: HashMode
  , useJson :: Bool
  }
  deriving Show

defaultDerivation = Derivation
  { name        = undefined
  , outputs     = Map.empty
  , inputs      = (Set.empty, Map.empty)
  , platform    = undefined
  , builder     = undefined
  , args        = []
  , env         = Map.empty
  , mFixed      = Nothing
  , hashMode    = Flat
  , useJson     = False
  }

data HashMode = Flat | Recursive
  deriving (Show, Eq)


defaultDerivationStrict' :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
defaultDerivationStrict' = fromValue @(AttrSet (NValue t f m)) >=> \s -> do
    (drv, ctx) <- runWithStringContextT' $ buildDerivationWithContext s
    name <- makeStorePathName $ name drv
    let inputs = toStorePaths ctx

    drv' <- case mFixed drv of
      Just (Store.SomeDigest digest) -> do
        let out = pathToText $ Store.makeFixedOutputPath "/nix/store" (hashMode drv == Recursive) digest name 
        let env' = if useJson drv then env drv else Map.insert "out" out (env drv)
        return $ drv { inputs, env = env', outputs = Map.singleton "out" out }

      Nothing -> do
        hash <- hashDerivationModulo $ drv 
          { inputs
          , env = if useJson drv then env drv
                  else foldl' (\m k -> Map.insert k "" m) (env drv) (Map.keys $ outputs drv)
          }
        outputs <- sequence $ Map.mapWithKey (\o _ -> makeOutputPath o hash name) (outputs drv)
        return $ drv 
          { inputs
          , outputs
          , env = if useJson drv then env drv else Map.union outputs (env drv)
          }

    drvPath <- writeDerivation drv'

    -- Todo: memoize this result here.
    -- _ <- hashDerivationModulo drv'

    let outputsWithContext = Map.mapWithKey (\out path -> principledMakeNixStringWithSingletonContext path (StringContext (pathToText drvPath) (DerivationOutput out))) (outputs drv')
    let drvPathWithContext = principledMakeNixStringWithSingletonContext (pathToText drvPath) (StringContext (pathToText drvPath) AllOutputs)
    -- TODO: Add location information for all the entries.
    return $ flip nvSet M.empty $ M.fromList $ map (second nvStr) $ ("drvPath", drvPathWithContext): Map.toList outputsWithContext

  where

    pathToText = Text.decodeUtf8 . Store.storePathToRawFilePath
    
    makeStorePathName name = case Store.makeStorePathName name of
      Left error -> throwError $ ErrorCall $ "Invalid name '" ++ show name ++ "' for use in a store path: " ++ error
      Right name -> return name

    makeOutputPath o h n = do
      name <- makeStorePathName (Store.unStorePathName n <> if o == "out" then "" else "-" <> o)
      return $ pathToText $ Store.makeStorePath "/nix/store" ("output:" <> Text.encodeUtf8 o) h name

    toStorePaths ctx = foldl (flip addToInputs) (Set.empty, Map.empty) ctx
    addToInputs (StringContext path kind) = case kind of
      DirectPath -> first (Set.insert path)
      DerivationOutput o -> second (Map.insertWith (++) path [o])
      AllOutputs -> 
        -- TODO: recursive lookup. See prim_derivationStrict
        -- XXX: When is this really used ?
        undefined

    writeDerivation (drv@Derivation {inputs, name}) = do
      let (inputSrcs, inputDrvs) = inputs
      references <- Set.fromList <$> (mapM parsePath $ Set.toList $ inputSrcs `Set.union` (Set.fromList $ Map.keys inputDrvs))
      path <- addTextToStore (Text.append name ".drv") (unparseDrv drv) (S.fromList $ Set.toList references) False
      parsePath $ Text.pack $ unStorePath path

    -- recurse the graph of inputDrvs to replace fixed output derivations with their fixed output hash
    -- this avoids propagating changes to their .drv when the output hash stays the same.
    hashDerivationModulo :: Derivation -> m (Store.Digest 'Store.SHA256)
    hashDerivationModulo drv@(Derivation {mFixed = Just (Store.SomeDigest (digest :: Store.Digest ht)), outputs, hashMode}) =
      case Map.toList outputs of
        [("out", path)] -> return $ Store.hash @'Store.SHA256 $ Text.encodeUtf8 $
          "fixed:out:" <> (if hashMode == Recursive then "r:" else "") <> (Store.algoName @ht) <> ":" <> (Store.encodeBase16 digest) <> ":" <> path
        outputsList -> throwError $ ErrorCall $ "This is weird. A fixed output drv should only have one outptu named 'out'. Got " ++ show outputsList 
    hashDerivationModulo drv@(Derivation {inputs = (inputSrcs, inputDrvs)}) = do
      inputsModulo <- Map.fromList <$> forM (Map.toList inputDrvs) (\(path, outs) -> do
        drv2 <- readDerivation $ Text.unpack path
        hash <- Store.encodeBase16 <$> hashDerivationModulo drv2
        return (hash, outs)
        )
      return $ Store.hash @'Store.SHA256 $ Text.encodeUtf8 $ unparseDrv (drv {inputs = (inputSrcs, inputsModulo)})

    unparseDrv :: Derivation -> Text
    unparseDrv (Derivation {..}) = Text.append "Derive" $ parens 
        [ -- outputs: [("out", "/nix/store/.....-out", "", ""), ...]
          list $ flip map (Map.toList outputs) (\(name, path) -> 
            let prefix = if hashMode == Recursive then "r:" else "" in
            case mFixed of
              Nothing -> parens [s name, s path, s "", s ""]
              Just (Store.SomeDigest (digest :: Store.Digest ht)) ->
                parens [s name, s path, s $ prefix <> Store.algoName @ht, s $ Store.encodeBase16 digest]
            )
        , -- inputDrvs
          list $ flip map (Map.toList $ snd inputs) (\(path, outs) ->
            parens [s path, list $ map s $ sort outs])
        , -- inputSrcs
          list (map s $ Set.toList $ fst inputs)
        , s platform
        , s builder
        , -- run script args
          list $ map s args
        , -- env (key value pairs)
          list $ flip map (Map.toList env) (\(k, v) ->
            parens [s k, s v])
        ]
      where
        parens :: [Text] -> Text
        parens ts = Text.concat ["(", Text.intercalate "," ts, ")"]
        list   :: [Text] -> Text
        list   ls = Text.concat ["[", Text.intercalate "," ls, "]"]
        s = Text.pack . show

    readDerivation :: String -> m Derivation
    readDerivation path = do
      content <- Text.decodeUtf8 <$> readFile path
      case parse derivationParser path content of
        Left error -> throwError $ ErrorCall $ "Failed to parse " ++ show path ++ ":\n" ++ show error
        Right drv -> return drv

    derivationParser :: Parser Derivation
    derivationParser = do
      _ <- string "Derive("
      -- outputs: [("out", "/nix/store/.....-out", "", ""), ...]
      fullOutputs <- list $
        fmap (\[n, p, ht, h] -> (n, p, ht, h)) $ parens s
      _ <- string ","
      inputDrvs <- fmap Map.fromList $ list $
        fmap (,) (string "(" *> s <* string ",") <*> (list s <* string ")")
      _ <- string ","
      inputSrcs <- fmap Set.fromList $ list s <* string ","
      platform  <- s                          <* string ","
      builder   <- s                          <* string ","
      args      <- list s                     <* string ","
      env <- fmap Map.fromList $ list $ fmap (\[a, b] -> (a, b)) $ parens s 
      _ <- string ")" <* eof

      let outputs = Map.fromList $ map (\(a, b, _, _) -> (a, b)) fullOutputs
      let (mFixed, hashMode) = parseFixed fullOutputs
      let name = "" -- FIXME (extract from file path ?)
      let useJson = ["__json"] == Map.keys env

      return $ Derivation {inputs = (inputSrcs, inputDrvs), ..}
     where
      s :: Parser Text
      s = fmap Text.pack $ string "\"" *> manyTill (escaped <|> regular) (string "\"")
      escaped = char '\\' *>
        (   '\n' <$ string "n"
        <|> '\r' <$ string "r"
        <|> '\t' <$ string "t"
        <|> anySingle
        )
      regular = noneOf ['\\', '"']

      parens :: Parser a -> Parser [a]
      parens p = (string "(") *> sepBy p (string ",") <* (string ")")
      list   p = (string "[") *> sepBy p (string ",") <* (string "]")

      parseFixed :: [(Text, Text, Text, Text)] -> (Maybe Store.SomeNamedDigest, HashMode)
      parseFixed fullOutputs = case fullOutputs of
        [("out", p, ht, h)] | ht /= "" && h /= "" ->
          let (ht, hashMode) = case Text.splitOn ":" ht of
                ["r", ht] -> (ht, Recursive)
                [ht] ->      (ht, Flat)
                _ -> undefined -- What ?! -- TODO: Throw a proper error
          in case Store.mkNamedDigest ht h of
            Right digest -> (Just digest, hashMode)
            Left error -> undefined -- TODO: Raise a proper parse error.
        _ -> (Nothing, Flat)


    parsePath p = case Store.parsePath "/nix/store" (Text.encodeUtf8 p) of
      Left err -> throwError $ ErrorCall $ "Cannot parse store path " ++ show p ++ ":\n" ++ show err
      Right path -> return path



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

          args        <- getAttrOr    "args"              (return [])      $ mapM (fromValue' >=> extractNixString)
          builder     <- getAttr      "builder"                            $ extractNixString
          platform    <- getAttr      "system"                             $ extractNoCtx >=> assertNonNull
          mHash       <- getAttrOr    "outputHash"        (return Nothing) $ extractNoCtx >=> (return . Just)
          hashMode    <- getAttrOr    "outputHashMode"    (return Flat)    $ extractNoCtx >=> parseHashMode
          outputs     <- getAttrOr    "outputs"           (return ["out"]) $ mapM (fromValue' >=> extractNoCtx)

          mFixedOutput <- case mHash of
            Nothing -> return Nothing
            Just hash -> do
              when (outputs /= ["out"]) $ lift $ throwError $ ErrorCall $ "Multiple outputs are not supported for fixed-output derivations"
              hashType <- getAttr "outputHashAlgo" $ extractNoCtx
              digest <- lift $ either (throwError . ErrorCall) return $ Store.mkNamedDigest hashType hash
              return $ Just digest

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
              return $ Map.singleton "__json" string
            else
              mapM (lift . coerceToString callFunc CopyToStore CoerceAny >=> extractNixString) $
                Map.fromList $ M.toList $ deleteAll [ "args", "__ignoreNulls" ] attrs

          return $ defaultDerivation { platform, builder, args, env,  hashMode, useJson
            , name = drvName
            , outputs = Map.fromList $ map (\o -> (o, "")) outputs
            , mFixed = mFixedOutput
            }
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

        -- Other helpers

        deleteAll :: [Text] -> AttrSet a -> AttrSet a
        deleteAll keys s = foldl' (flip M.delete) s keys


defaultTraceEffect :: MonadPutStr m => String -> m ()
defaultTraceEffect = Nix.Effects.putStrLn
