{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Nix.Effects.Basic where

import           Control.Monad
import           Control.Monad.State.Strict
import           Data.HashMap.Lazy              ( HashMap )
import qualified Data.HashMap.Lazy             as M
import           Data.List
import           Data.List.Split
import           Data.Maybe                     ( maybeToList )
import qualified Data.Set                      as S
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
                                                )
import           Nix.Expr
import           Nix.Frames
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

data Derivation = Derivation
  { outputs :: [ Text ]
  , inputSrcs :: S.Set (StorePath storeDir)
  , inputDrvs :: S.Set (StorePath storeDir)
  , platform :: Text
  , builder :: (StorePath storeDir)
  , args :: [ Text ]
  , env :: Either (M.HashMap Text Text) (JSONObject)
  }


-- static void prim_derivationStrict(EvalState & state, const Pos & pos, Value * * args, Value & v)
defaultDerivationStrict' :: forall e t f m . MonadNix e t f m => NValue t f m -> m (NValue t f m)
defaultDerivationStrict' 
-- {
--     state.forceAttrs(*args[0], pos);
  = fromValue @(AttrSet (NValue t f m)) >=> \s -> do
-- 
--     /* Figure out the name first (for stack backtraces). */
--     Bindings::iterator attr = args[0]->attrs->find(state.sName);
--     if (attr == args[0]->attrs->end())
--         throw EvalError(format("required attribute 'name' missing, at %1%") % pos);
--
--     string drvName;
--     Pos & posDrvName(*attr->pos);
--     try {
--         drvName = state.forceStringNoCtx(*attr->value, pos);
--     } catch (Error & e) {
--         e.addPrefix(format("while evaluating the derivation attribute 'name' at %1%:\n") % posDrvName);
--         throw;
--     }
-- 
    drvName <- demandAttr "name" s

--     /* Check whether attributes should be passed as a JSON file. */
--     std::ostringstream jsonBuf;
--     std::unique_ptr<JSONObject> jsonObject;
--     attr = args[0]->attrs->find(state.sStructuredAttrs);
--     if (attr != args[0]->attrs->end() && state.forceBool(*attr->value, pos))
--         jsonObject = std::make_unique<JSONObject>(jsonBuf);
    structuredAttrs <- maybeForceAttr False "__structuredAttrs" s

-- 
--     /* Check whether null attributes should be ignored. */
--     bool ignoreNulls = false;
--     attr = args[0]->attrs->find(state.sIgnoreNulls);
--     if (attr != args[0]->attrs->end())
--         ignoreNulls = state.forceBool(*attr->value, pos);
    ignoreNulls <- maybeForceAttr False "__ignoreNulls" s


--                     if (i->name == state.sBuilder) drv.builder = s;
--                     else if (i->name == state.sSystem) drv.platform = s;
--                     else if (i->name == state.sOutputHash) outputHash = s;
--                     else if (i->name == state.sOutputHashAlgo) outputHashAlgo = s;
--                     else if (i->name == state.sOutputHashMode) handleHashMode(s);
--                     else if (i->name == state.sOutputs)

    builder <- demandAttr "builder" s
    platform <- demandAttr "system" s
    outputHash <- {- ensureValid <$> -} demandMaybeAttr "outputHash" s
    outputHashAlgo <- {- ensureValid <$> -} demandMaybeAttr "outputHashAlgo" s
    outputHashRecursive <- {- handleHashMode <$> -} maybeForceAttr "flat" "outputHashMode" s
    outputs <- {- handleoutputs <$> -} maybeForceAttr [ "out" ] "outputs" s

-- 
--     /* Build the derivation expression by processing the attributes. */
--     Derivation drv;
-- 
--     PathSet context;
--     TODO: Handle context
-- 
--     std::optional<std::string> outputHash;
--     std::string outputHashAlgo;
--     bool outputHashRecursive = false;
-- 
--     StringSet outputs;
--     outputs.insert("out");
-- 
--     for (auto & i : args[0]->attrs->lexicographicOrder()) {
--         if (i->name == state.sIgnoreNulls) continue;
--         const string & key = i->name;
--         vomit("processing attribute '%1%'", key);
--         auto handleHashMode = [&](const std::string & s) {
--             if (s == "recursive") outputHashRecursive = true;
--             else if (s == "flat") outputHashRecursive = false;
--             else throw EvalError("invalid value '%s' for 'outputHashMode' attribute, at %s", s, posDrvName);
--         };
-- 
--         auto handleOutputs = [&](const Strings & ss) {
--             outputs.clear();
--             for (auto & j : ss) {
--                 if (outputs.find(j) != outputs.end())
--                     throw EvalError(format("duplicate derivation output '%1%', at %2%") % j % posDrvName);
--                 /* !!! Check whether j is a valid attribute
--                    name. */
--                 /* Derivations cannot be named ‘drv’, because
--                    then we'd have an attribute ‘drvPath’ in
--                    the resulting set. */
--                 if (j == "drv")
--                     throw EvalError(format("invalid derivation output name 'drv', at %1%") % posDrvName);
--                 outputs.insert(j);
--             }
--             if (outputs.empty())
--                 throw EvalError(format("derivation cannot have an empty set of outputs, at %1%") % posDrvName);
--         };
-- 
--         try {
--         
--             if (ignoreNulls) {
--                 state.forceValue(*i->value);
--                 if (i->value->type == tNull) continue;
--             }
--
--             /* The `args' attribute is special: it supplies the
--                command-line arguments to the builder. */
--             if (i->name == state.sArgs) {
--                 state.forceList(*i->value, pos);
--                 for (unsigned int n = 0; n < i->value->listSize(); ++n) {
--                     string s = state.coerceToString(posDrvName, *i->value->listElems()[n], context, true);
--                     drv.args.push_back(s);
--                 }
--             }
--             
--             /* All other attributes are passed to the builder through
--                the environment. */
--             else {
-- 
--                 if (jsonObject) {
-- 
--                     if (i->name == state.sStructuredAttrs) continue;
-- 
--                     auto placeholder(jsonObject->placeholder(key));
--                     printValueAsJSON(state, true, *i->value, placeholder, context);
-- 
--                     if (i->name == state.sBuilder)
--                         drv.builder = state.forceString(*i->value, context, posDrvName);
--                     else if (i->name == state.sSystem)
--                         drv.platform = state.forceStringNoCtx(*i->value, posDrvName);
--                     else if (i->name == state.sOutputHash)
--                         outputHash = state.forceStringNoCtx(*i->value, posDrvName);
--                     else if (i->name == state.sOutputHashAlgo)
--                         outputHashAlgo = state.forceStringNoCtx(*i->value, posDrvName);
--                     else if (i->name == state.sOutputHashMode)
--                         handleHashMode(state.forceStringNoCtx(*i->value, posDrvName));
--                     else if (i->name == state.sOutputs) {
--                         /* Require ‘outputs’ to be a list of strings. */
--                         state.forceList(*i->value, posDrvName);
--                         Strings ss;
--                         for (unsigned int n = 0; n < i->value->listSize(); ++n)
--                             ss.emplace_back(state.forceStringNoCtx(*i->value->listElems()[n], posDrvName));
--                         handleOutputs(ss);
--                     }
-- 
--                 } else {
--                     auto s = state.coerceToString(posDrvName, *i->value, context, true);
--                     drv.env.emplace(key, s);
--                     if (i->name == state.sBuilder) drv.builder = s;
--                     else if (i->name == state.sSystem) drv.platform = s;
--                     else if (i->name == state.sOutputHash) outputHash = s;
--                     else if (i->name == state.sOutputHashAlgo) outputHashAlgo = s;
--                     else if (i->name == state.sOutputHashMode) handleHashMode(s);
--                     else if (i->name == state.sOutputs)
--                         handleOutputs(tokenizeString<Strings>(s));
--                 }
-- 
--             }
-- 
--         } catch (Error & e) {
--             e.addPrefix(format("while evaluating the attribute '%1%' of the derivation '%2%' at %3%:\n")
--                 % key % drvName % posDrvName);
--             throw;
--         }
--     }
-- 
--     if (jsonObject) {
--         jsonObject.reset();
--         drv.env.emplace("__json", jsonBuf.str());
--     }
-- 
--     /* Everything in the context of the strings in the derivation
--        attributes should be added as dependencies of the resulting
--        derivation. */
--     for (auto & path : context) {
-- 
--         /* Paths marked with `=' denote that the path of a derivation
--            is explicitly passed to the builder.  Since that allows the
--            builder to gain access to every path in the dependency
--            graph of the derivation (including all outputs), all paths
--            in the graph must be added to this derivation's list of
--            inputs to ensure that they are available when the builder
--            runs. */
--         if (path.at(0) == '=') {
--             /* !!! This doesn't work if readOnlyMode is set. */
--             PathSet refs;
--             state.store->computeFSClosure(string(path, 1), refs);
--             for (auto & j : refs) {
--                 drv.inputSrcs.insert(j);
--                 if (isDerivation(j))
--                     drv.inputDrvs[j] = state.store->queryDerivationOutputNames(j);
--             }
--         }
-- 
--         /* Handle derivation outputs of the form ‘!<name>!<path>’. */
--         else if (path.at(0) == '!') {
--             std::pair<string, string> ctx = decodeContext(path);
--             drv.inputDrvs[ctx.first].insert(ctx.second);
--         }
-- 
--         /* Otherwise it's a source file. */
--         else
--             drv.inputSrcs.insert(path);
--     }
-- 
--     /* Do we have all required attributes? */
--     if (drv.builder == "")
--         throw EvalError(format("required attribute 'builder' missing, at %1%") % posDrvName);
--     if (drv.platform == "")
--         throw EvalError(format("required attribute 'system' missing, at %1%") % posDrvName);
-- 
--     /* Check whether the derivation name is valid. */
--     checkStoreName(drvName);
--     if (isDerivation(drvName))
--         throw EvalError(format("derivation names are not allowed to end in '%1%', at %2%")
--             % drvExtension % posDrvName);
    (env, inputSrcs, inputDrvs) <- if structuredAttrs
      then Right <$> toJson $ deleteAll [ "__ignoreNulls" "__structuredAttrs" ] s
      else Left <$> forceToString $ deleteAll [ "__ignoreNulls" ] s

-- 
--     if (outputHash) {
--         /* Handle fixed-output derivations. */
--         if (outputs.size() != 1 || *(outputs.begin()) != "out")
--             throw Error(format("multiple outputs are not supported in fixed-output derivations, at %1%") % posDrvName);
-- 
--         HashType ht = outputHashAlgo.empty() ? htUnknown : parseHashType(outputHashAlgo);
--         Hash h(*outputHash, ht);
-- 
--         Path outPath = state.store->makeFixedOutputPath(outputHashRecursive, h, drvName);
--         if (!jsonObject) drv.env["out"] = outPath;
--         drv.outputs["out"] = DerivationOutput(outPath,
--             (outputHashRecursive ? "r:" : "") + printHashType(h.type),
--             h.to_string(Base16, false));
--     }
-- 
--     else {
--         /* Construct the "masked" store derivation, which is the final
--            one except that in the list of outputs, the output paths
--            are empty, and the corresponding environment variables have
--            an empty value.  This ensures that changes in the set of
--            output names do get reflected in the hash. */
--         for (auto & i : outputs) {
--             if (!jsonObject) drv.env[i] = "";
--             drv.outputs[i] = DerivationOutput("", "", "");
--         }
-- 
--         /* Use the masked derivation expression to compute the output
--            path. */
--         Hash h = hashDerivationModulo(*state.store, drv);
-- 
--         for (auto & i : drv.outputs)
--             if (i.second.path == "") {
--                 Path outPath = state.store->makeOutputPath(i.first, h, drvName);
--                 if (!jsonObject) drv.env[i.first] = outPath;
--                 i.second.path = outPath;
--             }
--     }
-- 
--     /* Write the resulting term into the Nix store directory. */
--     Path drvPath = writeDerivation(state.store, drv, drvName, state.repair);
-- 
--     printMsg(lvlChatty, format("instantiated '%1%' -> '%2%'")
--         % drvName % drvPath);
    path <- {- writeDerivation $ -} case outputHash of
      Nothing -> error "not implemented" -- Derivation outputs inputSrcs inputDrvs platform builder args env
      Just hash -> error "not implemented" -- fixedOutputDerivation

--     /* Optimisation, but required in read-only mode! because in that
--        case we don't actually write store derivations, so we can't
--        read them later. */
--     drvHashes[drvPath] = hashDerivationModulo(*state.store, drv);
    -- XXX We have a readonly store for this !

-- 
--     state.mkAttrs(v, 1 + drv.outputs.size());
--     mkString(*state.allocAttr(v, state.sDrvPath), drvPath, {"=" + drvPath});
--     for (auto & i : drv.outputs) {
--         mkString(*state.allocAttr(v, state.symbols.create(i.first)),
--             i.second.path, {"!" + i.first + "!" + drvPath});
--     }
--     v.attrs->sort();
-- }
    let resultAttrs = [ ("drvPath", Direct path) ] ++ map (\o -> (o, Indirect o path))
    return $ nvSet (M.fromList resultAttrs) M.null
 where
  demandAttr n s = maybeForceAttr (error "Required attribute '" ++ n ++ "' not found.") n s
  maybeForceAttr d n s = maybe (pure d) (demand ?? fromValue) (M.lookup n s)
  demandMaybeAttr n s = (demand ?? fromValue) <$> (M.lookup n s)
  deleteAll keys s = foldl' (flip M.delete) s keys

defaultTraceEffect :: MonadPutStr m => String -> m ()
defaultTraceEffect = Nix.Effects.putStrLn
