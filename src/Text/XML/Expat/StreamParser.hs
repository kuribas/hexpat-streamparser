{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}

{-|
Module      : Text.XML.Expat.StreamParser
Description : Streaming parsers using hexpat
Copyright   : (c) Kristof Bastiaensen, 2020
License     : BSD-3
Maintainer  : kristof@resonata.be
Stability   : unstable
Portability : ghc

This module implements a streaming parser built on top of hexpat. It
has an interface similar to parsec and other parser libraries.  Note
that backtracking is not supported.  Only the current tag name and
attributes can be looked at without backtracking.  After a /tag test/
and /attribute parser/ has succeeded, attempting to backtrack will
generate an error.

This library can be used with a streaming library (conduit, pipes,
etc...) by providing an instance for `List`.
-}

module Text.XML.Expat.StreamParser
  (
    -- * Event parser datatype
    EventListParser
  , EventParser
  , EventLoc
  , EventParseError (..)
  , runEventParser
  , customError
  , -- * Running parsers
    parseXMLByteString
  , parseXMLFile
  , -- * Attribute parsers
    AttrParser
  , ParseAttr
  , getAttr
  , peekAttr
  , findAttr
  , skipAttrs
  , noAttrs
  , -- * Event parsers
    someTag
  , skipTag
  , skipTags
  , skipTagsTill
  , tag
  , someEmptyTag
  , emptyTag
  , text
    -- * Re-exports from "Control.Applicative.Combinators"
  ,  (C.<|>)
  , C.optional
  , C.empty
    -- * Re-exports from "Control.Monad.Combinators"
  , C.between
  , C.choice
  , count
  , count'
  , C.eitherP
  , endBy
  , endBy1
  , many
  , manyTill
  , manyTill_
  , C.some
  , someTill
  , someTill_
  , C.option
  , sepBy
  , sepBy1
  , sepEndBy
  , sepEndBy1
  , skipMany
  , skipSome
  , skipCount
  , skipManyTill
  , skipSomeTill
  ) where

import Control.Applicative hiding (many)
import Control.Monad.Combinators as C
import Control.Monad.Error.Class
import Control.Monad.Fail
import Control.Monad.State hiding (fail, lift)
import Control.Monad.Trans (lift)
import qualified Data.ByteString.Lazy as LazyBS
import System.IO
import Data.Functor.Identity
import Data.Bifunctor
import Data.String
import qualified Data.List.Class as List
import Data.List.Class (ItemM, List, ListItem(..))
import qualified Data.Text as Text
import Data.Text (Text)
import Text.XML.Expat.SAX as Expat
import Data.List (nub)

newtype CPSExceptT e m a =
  CPSExceptT { getCPSExceptT :: forall r. ((e -> m r) -> (a -> m r) -> m r) }

runCPSExceptT :: Applicative m => CPSExceptT e m a -> m (Either e a)
runCPSExceptT (CPSExceptT f) = f (pure . Left)  (pure . Right)
{-# INLINE runCPSExceptT #-}

instance Functor (CPSExceptT e m) where
  fmap f (CPSExceptT g) = CPSExceptT $ \failC successC ->
    g failC (successC . f)
  {-# INLINE fmap #-}

instance Monad m => Applicative (CPSExceptT e m) where
  pure x = CPSExceptT $ \_failC successC -> successC x
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad m => Monad (CPSExceptT e m) where
  CPSExceptT f >>= g = CPSExceptT $ \failC successC ->
    f failC (\a -> getCPSExceptT (g a) failC successC)
  {-# INLINE (>>=) #-}

instance Monad m => MonadError e (CPSExceptT e m) where
  throwError e = CPSExceptT $ \failC _successC -> failC e
  {-# INLINE throwError #-}
  catchError (CPSExceptT f) handler =
    CPSExceptT $ \failC successC ->
    f (\e -> getCPSExceptT (handler e) failC successC)
    successC
  {-# INLINE catchError #-}

instance MonadTrans (CPSExceptT e) where
  lift m = CPSExceptT $ \_failC successC -> m >>= successC
  {-# INLINE lift #-}

instance MonadState s m => MonadState s (CPSExceptT e m) where
  state f = lift $ state f
  {-# INLINE state #-}

type EventLoc = (SAXEvent Text Text, XMLParseLocation)

type Attrs = [(Text, Text)]

data SAXStream l = Ordered (ListItem l EventLoc)

data ParserState l = ParserState Bool (SAXStream l)

data EventParseError e =
  EndOfSaxStream |
  Empty |
  ExpectedTag |
  UnMatchedTag |
  ExpectedCloseTag |
  XmlError XMLParseError |
  AttributeNotFound (Maybe Text) Text |
  UnknownAttributes [Text]|
  Expected [Text] |
  CustomError e
  deriving (Show, Eq)

data AttrParserError e =
  AttrRequired Text |
  AttrEmpty |
  CustomAttrError e
  deriving (Show, Eq)

attrErrorToEvent :: AttrParserError e -> EventParseError e
attrErrorToEvent AttrEmpty = Empty
attrErrorToEvent (AttrRequired t) = AttributeNotFound Nothing t
attrErrorToEvent (CustomAttrError e) = CustomError e

-- | semigroup instance concatenates Expected tags.
instance Semigroup (EventParseError e) where
  e <> Empty = e
  Expected t <> Expected s = Expected $ t ++ s
  AttributeNotFound (Just t) _ <> Expected s = Expected $ t: s
  Expected t <> AttributeNotFound (Just s) _ = Expected $ t ++ [s]
  AttributeNotFound (Just s) _ <> AttributeNotFound (Just t) _ =
    Expected $ nub [s, t]
  _ <> e = e

instance Monoid (EventParseError e) where
  mempty = Empty

-- | A parser that parses a lazy list of SAX events into a value of
-- type `a`, or an error of type `@EventParseError@ e`, where `e` is a
-- custom error type.
type EventListParser e a = EventParser [] e Identity a
     
-- | A parser that parses a stream of SAX events of type @l
-- `EventLoc`@ into to a value of type @a@ using `m` as the underlying
-- monad.  l should be an instance of `List`, and m should be equal to
-- the type instance (@`ItemM` l@).  Custom error messages are
-- possible using the type e.
newtype EventParser l e m a = EventParser
  { getEventParser :: CPSExceptT (EventParseError e) (StateT (ParserState l) m)
                      a
  } deriving (Functor, Applicative, Monad, MonadError (EventParseError e))

-- | Throw an error with a custom type.  If the custom error type
-- provides an `IsString` instance, you can also use `fail` (for example
-- Text, String).
customError :: Monad m => e -> EventParser l e m a
customError = throwError . CustomError

instance (Monad m, IsString e) => MonadFail (EventParser l e m) where
  fail = throwError . CustomError . fromString

-- | A parser for the attributes of a single tag, that returns a value
-- of type a.  Custom error messages are possible of type e.
newtype AttrParser e a = AttrParser
  { runAttrParser :: StateT Attrs (Either (AttrParserError e)) a
  } deriving (Functor, Applicative, Monad, MonadError (AttrParserError e))

instance Alternative (AttrParser e) where
  p <|> q = p `catchError` const q
  empty = throwError AttrEmpty

instance Semigroup a => Semigroup (AttrParser e a) where
  (<>) = liftA2 (<>)

instance Monoid a => Monoid (AttrParser e a) where
  mempty = pure mempty

-- | A parser for the value of an attribute
class ParseAttr e a where
  parseAttr :: Text -> Either e a

instance ParseAttr e Text where
  parseAttr = pure

instance MonadTrans (EventParser l e) where
  lift m = EventParser $ lift $ lift m

-- set consumed state, and return old consumed state
setConsumedState :: Monad m => Bool -> EventParser l e m Bool
setConsumedState newState = EventParser $ do
  ParserState oldState stream <- get
  put $ ParserState newState stream
  pure oldState

-- combine old and new consumed state
updateConsumedState :: Monad m => Bool -> EventParser l e m ()
updateConsumedState oldState = EventParser $ do
  ParserState newState stream <- get
  put $ ParserState (oldState || newState) stream

instance Monad m => Alternative (EventParser l e m) where
  EventParser p <|> EventParser q = EventParser $ do
    -- clear consumed state
    oldConsumedState <- getEventParser $ setConsumedState False
    res <- catchError p $ \err -> do
      ParserState pConsumed _ <- get
      if pConsumed
        -- don't backtrack when already consumed some state
        then throwError err
        else catchError q $ \err2 ->
        do ParserState qConsumed _ <- get
           if qConsumed
             then throwError err2
             else do
             -- if nothing consumed, then reset consumed state and
             -- combine error messages
             getEventParser $ updateConsumedState oldConsumedState
             throwError (err <> err2)
    getEventParser $ updateConsumedState oldConsumedState
    pure res

  empty = EventParser $ throwError Empty

instance Monad m => MonadPlus (EventParser l e m) where
  mplus = (<|>)
  mzero = empty

instance (Monad m, Semigroup a) => Semigroup (EventParser l e m a) where
  (<>) = liftA2 (<>)

instance (Monad m, Monoid a) => Monoid (EventParser l e m a) where
  mempty = pure mempty

-- run a parser
runEventParser
  :: List l
  => EventParser l e (ItemM l) a  -- ^ parser to run
  -> l EventLoc                   -- ^ list of SAX event
  -> (ItemM l) (Either (EventParseError e, Maybe XMLParseLocation) a)
runEventParser (EventParser parser) events = do
  firstItem <- List.runList events
  let initState = ParserState False (Ordered firstItem)
  do (a, ParserState _ (Ordered item)) <-
       flip runStateT initState $ runCPSExceptT parser
     case a of
       Right res -> pure $ Right res
       Left err -> pure $ Left $ case item of
         Nil -> (err, Nothing)
         (Cons (_, loc) _) -> (err, Just loc)

-- | Parse a lazy bytestring with the given parser.  Evaluating the
-- result to WHNF will consume the bytestring (as much as needed).
-- However this function does not close resources, for example a file
-- handle when using `readFile`.  Make sure to always explicitly close
-- a resource, /after/ evaluating to WHNF, or use the streaming
-- version of this library (hexpat-streamparser-conduit).  For reading
-- from a file use the `parseXMLFile` function.
parseXMLByteString :: EventListParser e a
                   -> Expat.ParseOptions Text Text
                   -> LazyBS.ByteString
                   -> Either (EventParseError e, Maybe XMLParseLocation) a
parseXMLByteString parser parseOptions bs =
  runIdentity $ runEventParser parser $ Expat.parseLocations parseOptions bs

-- | Lazily parse an xml file into a value.  This function ensures the
--  input is consumed and the file handle closed, before returning the
--  value.
parseXMLFile :: Expat.ParseOptions Text Text
             -> IOMode
             -> FilePath
             -> EventListParser e a
             -> IO (Either (EventParseError e, Maybe XMLParseLocation) a)
parseXMLFile parseOptions mode fp parser =
  withFile fp mode $ \h -> do
  bs <- LazyBS.hGetContents h
  pure $! parseXMLByteString parser parseOptions bs

-- skip to next open tag.  Skip whitespace text if any. This doesn't
-- consume any tags.
skipToNextTag :: forall l e. (List l, Monad (ItemM l))
              => EventParser l e (ItemM l) ()
skipToNextTag =
  EventParser $ do
    ParserState consumed (Ordered firstItem) <- get
    let loop item =
          case item of
            Nil -> throwError EndOfSaxStream
            list@(Cons (eventTag, _loc) next) ->
              case eventTag of
                StartElement _ _ -> pure list
                EndElement _ -> do
                  put $ ParserState consumed (Ordered list)
                  throwError ExpectedTag
                CharacterData t
                  | not (Text.all (`elem` (" \t\r\n" :: String)) t) -> pure list
                FailDocument err -> do
                  put $ ParserState consumed (Ordered list)
                  throwError $ XmlError err
                _ -> do
                  nextItem <- getEventParser $ lift $ List.runList next
                  loop nextItem
    lastList <- loop firstItem
    put $ ParserState consumed (Ordered lastList)

-- skip to after closed tag, or raise an error
closeTag :: forall l e. (List l, Monad (ItemM l))
         => Text
         -> EventParser l e (ItemM l) ()
closeTag tagName =
  EventParser $ do
    ParserState consumed (Ordered firstItem) <- get
    let loop item =
          case item of
            Nil -> throwError EndOfSaxStream
            list@(Cons (eventTag, _loc) next) ->
              case eventTag of
                EndElement tagName2
                  | tagName2 == tagName ->
                    getEventParser $ lift $ List.runList next
                  | otherwise -> throwError UnMatchedTag
                StartElement _ _ -> throwError ExpectedCloseTag
                CharacterData t
                  | not (Text.all (`elem` (" \t\r\n" :: String)) t) ->
                    throwError ExpectedCloseTag
                FailDocument err -> do
                  put $ ParserState consumed (Ordered list)
                  throwError $ XmlError err
                _ -> do
                  nextItem <- getEventParser $ lift $ List.runList next
                  loop nextItem
    lastList <- loop firstItem
    put $ ParserState consumed (Ordered lastList)

lookupRemove :: (Eq k) => k -> [(k, v)] -> Maybe (v, [(k, v)])
lookupRemove _ [] = Nothing
lookupRemove k1 ((k2, v):rest)
  | k1 == k2 = Just (v, rest)
  | otherwise = second ((k2, v) :) <$> lookupRemove k1 rest

-- | returns the value for the given attribute.  Fail if the attribute
-- is not found.
getAttr :: ParseAttr e a
        => Text            -- ^ attribute name
        -> AttrParser e a
getAttr attr =
  AttrParser $ do
    attrs <- get
    case lookupRemove attr attrs of
      Nothing -> throwError $ AttrRequired attr
      Just (v, st) -> do
        put st
        either (throwError . CustomAttrError) pure $ parseAttr v

-- | return the value for the attribute if it exists, otherwise
-- @Nothing@.
findAttr :: ParseAttr e a
         => Text                    -- ^ attribute name
         -> AttrParser e (Maybe a)
findAttr attr =
  catchError (Just <$> getAttr attr) $ \err ->
  case err of
    (AttrRequired _) -> pure Nothing
    _ -> throwError err
    
-- | run an attribute parser without consuming any attributes.
peekAttr :: AttrParser e a -> AttrParser e a
peekAttr (AttrParser attrP) =
  AttrParser $ do
    attrs <- get
    attrP <* put attrs

-- | consume all remaining attributes
skipAttrs :: AttrParser e ()
skipAttrs = AttrParser $ put []

-- | expect no attributes.  This is the same as `pure ()`
noAttrs :: AttrParser e ()
noAttrs = pure ()

-- | Parse a tag that succeed on the given test function.  Parses the
-- children in the order or the inner parser.
someTag :: (Monad (ItemM l), List l)
        => (Text -> Bool)     -- ^ tagname test
        -> AttrParser e b     -- ^ parser for attributes
        -> (b -> EventParser l e (ItemM l) a) -- ^ parser for tag children
        -> EventParser l e (ItemM l) a
someTag tagnameTest attrParser inner = EventParser $ do
  _ <- getEventParser skipToNextTag
  ParserState _ elems <- get
  case elems of
    Ordered Nil -> throwError EndOfSaxStream
    Ordered (Cons (StartElement tagName attrs, _loc) next)
      | tagnameTest tagName ->
          case runStateT (runAttrParser attrParser) attrs of
            Left err -> throwError $ attrErrorToEvent err
            Right (attrData, []) -> do
              nextItem <- getEventParser $ lift $ List.runList next
              put $ ParserState True (Ordered nextItem)
              result <- getEventParser $ inner attrData
              getEventParser $ closeTag tagName
              pure result
            Right (_, attributes) ->
              throwError $ UnknownAttributes $ map fst attributes
      | otherwise -> throwError ExpectedTag
    Ordered _ -> throwError ExpectedTag
{-# INLINABLE someTag #-}    

--  UnOrdered [] -> throwError "Unexpected end of input."
--  UnOrdered lst -> _ 
-- -- | 
-- someUnorderedTag  :: (Monad (ItemM l), List l)
--                   => (Text -> Bool)
--                   -> AttrParser b
--                   -> (b -> EventParser l (ItemM l) a)
--                   -> EventParser l (ItemM l) a
-- someUnorderedTag inner = _
-- | Skip next tag
skipTag :: (Monad (ItemM l), List l) => EventParser l e (ItemM l) ()
skipTag = someTag (const True) skipAttrs $ const skipTags
{-# INLINE skipTag #-}          

-- | Skip remaining tags and text, if any.
skipTags :: (Monad (ItemM l), List l) => EventParser l e(ItemM l) ()
skipTags = optional text >> skipMany (skipTag >> void text)

-- | Skip zero or more tags until the given parser succeeds
skipTagsTill ::
     (Monad (ItemM l), List l)
  => EventParser l e (ItemM l) a
  -> EventParser l e (ItemM l) a
skipTagsTill = skipManyTill skipTag

-- | Parse a tag with the given name, using the inner parser for the
-- children tags.
tag :: (Monad (ItemM l), List l)
    => Text                     -- ^ tag name
    -> AttrParser e b           -- ^ attribute parser
    -> (b -> EventParser l e (ItemM l) a) -- ^ tag children parser
    -> EventParser l e (ItemM l) a
tag name attrP children =
  catchError (someTag (== name) attrP children) $ \err ->
  case err of
    ExpectedTag -> throwError $ Expected [name]
    AttributeNotFound Nothing a -> throwError $ AttributeNotFound (Just name) a
    _ -> throwError err
    
-- -- | Parse a tag with the given name, using the inner parser for the
-- -- children tags.  The children tags can be in any order.  Note that
-- -- this is less efficient than an orderedTag, since it has to keep
-- -- track of all unmatched tags.
-- -- unorderedTag :: (Monad (ItemM l), List l)
-- --              => Text
-- --              -> AttrParser b
-- --              -> (b -> EventParser l (ItemM l) a)
-- --              -> EventParser l (ItemM l) a
-- -- unorderedTag name = someUnorderedTag (==name)

-- | Parse a tag which should have no children.
someEmptyTag :: (Monad (ItemM l), List l)
             => (Text -> Bool)   -- ^ tag name test
             -> AttrParser e b   -- ^ attribute parser
             -> EventParser l e (ItemM l) b
someEmptyTag tagnameTest attrP = someTag tagnameTest attrP pure

-- | Parser a tag with the given name which should have no children.
-- If the tag has children, an error is raised.
emptyTag :: (Monad (ItemM l), List l)
         => Text                 -- ^ tag name
         -> AttrParser e b       -- ^ attribute parser
         -> EventParser l e (ItemM l) b
emptyTag name = someEmptyTag (== name)

-- | Parse text.  Note that parsing a tag will skip white space, so if
-- whitespace is significant, run this parser first.
text :: (Monad (ItemM l), List l) => EventParser l e (ItemM l) Text
text = EventParser $ do
  ParserState consumed (Ordered firstItem) <- get
  let loop item =
        case item of
          Nil -> throwError EndOfSaxStream
          (Cons (eventTag, _loc) next) ->
            case eventTag of
              CharacterData textData -> do
                nextItem <- getEventParser $ lift $ List.runList next
                second (textData :) <$> loop nextItem
              StartElement _ _ -> pure (item, [])
              EndElement _ -> pure (item, [])
              FailDocument err -> throwError $ XmlError err
              _ -> loop =<< getEventParser (lift $ List.runList next)
  (lastList, texts) <- loop firstItem
  put $ ParserState consumed (Ordered lastList)
  pure $ Text.concat $ reverse texts
