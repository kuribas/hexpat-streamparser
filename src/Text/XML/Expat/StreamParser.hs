{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables#-}
{-# LANGUAGE FlexibleContexts #-}
module Text.XML.Expat.StreamParser where
import Data.Bifunctor
import Control.Monad.Trans (lift)
import Control.Monad.State hiding (fail, lift)
import Control.Applicative hiding (many)
import Control.Monad.Except hiding (fail, lift)
import Control.Monad.Fail
import Control.Monad.Reader hiding (fail, lift)
import qualified Data.List.Class as List
import Data.List.Class (List, ItemM, ListItem(..))
import Text.XML.Expat.SAX
import qualified Data.Text as Text
import Data.Text (Text)
import Control.Monad.Combinators

type EventLoc = (SAXEvent Text Text, XMLParseLocation)
type Attrs = [(Text, Text)]

data SAXStream l =
  -- list for unordered parsers
  -- UnOrdered [EventLoc] |
  -- stream for ordered parsers.
  Ordered (ListItem l EventLoc)

data ParserState l = ParserState Bool (SAXStream l)

newtype EventParser l m a =
  EventParser { runEventParser ::
                  ExceptT Text (ReaderT Attrs (StateT (ParserState l) m)) a }
  deriving (Functor, Applicative, Monad, MonadError Text)

newtype AttrParser a =
  AttrParser {runAttrParser :: StateT Attrs (Either Text) a}
  deriving (Functor, Applicative, Monad, MonadError Text)

class ParserAttr a where
  parseAttr :: Text -> Either Text a

-- skip to next open tag.  Skip whitespace text if any. This doesn't
-- consume any tags.
skipToNextTag :: forall l.(List l, Monad (ItemM l))
              => EventParser l (ItemM l) ()
skipToNextTag = EventParser $ do
  ParserState consumed (Ordered firstItem) <- get
  let loop item = case item of
        Nil -> throwError "unexpected end of file"
        list@(Cons (eventTag, _) next) -> case eventTag of
          StartElement _ _ -> pure list
          EndElement _ -> throwError "expected tag"
          CharacterData t |
            not (Text.all (`elem` (" \t\r\n" :: String)) t) -> pure list
          FailDocument err -> throwError $ Text.pack $ show err
          _ -> do nextItem <- liftItemM $ List.runList next
                  loop nextItem
  lastList <- loop firstItem
  put $ ParserState consumed (Ordered lastList)

-- skip to after closed tag, or raise an error
closeTag :: forall l.(List l, Monad (ItemM l))
         => Text -> EventParser l (ItemM l) ()
closeTag tagName = EventParser $ do
  ParserState consumed (Ordered firstItem) <- get
  let loop item = case item of
        Nil -> throwError "unexpected end of file"
        list@(Cons (eventTag, _) next) -> case eventTag of
          EndElement tagName2 
            | tagName2 == tagName -> pure list
            | otherwise -> error "expected closing tag"
          StartElement _ _ -> error "unexpected tag"
          CharacterData t |
            not (Text.all (`elem` (" \t\r\n" :: String)) t) ->
              error "unexpected text"
          FailDocument err -> throwError $ Text.pack $ show err
          _ -> do nextItem <- liftItemM $ List.runList next
                  loop nextItem
  lastList <- loop firstItem
  put $ ParserState consumed (Ordered lastList)

liftItemM :: Monad m
          => m a
          -> ExceptT Text (ReaderT Attrs (StateT (ParserState l) m)) a
liftItemM = lift . lift . lift

lookupRemove :: (Eq k) => k -> [(k, v)] -> Maybe (v, [(k, v)])
lookupRemove _ [] = Nothing
lookupRemove k1 ((k2, v):rest)
  | k1 == k2 = Just (v,rest)
  | otherwise = second ((k2, v):) <$> lookupRemove k1 rest

-- | an attribute parser which returns the value for that attribute.
getAttr :: ParserAttr a => Text -> AttrParser a
getAttr attr = AttrParser $ do
  attrs <- get
  case lookupRemove attr attrs of
    Nothing -> throwError $ "Attribute " <> attr <> " required."
    Just (v, st) ->
      do put st;
         either throwError pure $ parseAttr v

-- | run an attribute parser without consuming any attributes.
peekAttr :: AttrParser a -> AttrParser a 
peekAttr (AttrParser attrP) = AttrParser $ do
  attrs <- get
  attrP <* put attrs

-- | consume all remaining attributes
skipAttrs :: AttrParser ()
skipAttrs = AttrParser $ put []

emptyAttrs :: AttrParser ()
emptyAttrs = AttrParser $ do
  attrs <- get
  unless (null attrs) $
    throwError "unexpected attributes"
  
instance Monad m => MonadFail (EventParser l m) where
  fail s = throwError $ Text.pack s 

instance Monad m => Alternative (EventParser l m) where
  p <|> q = 
    catchError p $ \err -> EventParser $ do
      ParserState consumed _ <- get
      if consumed
        then throwError err
        else runEventParser q
        
  empty = throwError "Parse failure: empty"

instance Monad m => MonadPlus (EventParser l m) where
  mplus = (<|>)
  mzero = empty

liftListT :: Monad (ItemM l)
          => ItemM l a
          -> ExceptT Text (ReaderT Attrs (StateT (ParserState l) (ItemM l))) a
liftListT = lift . lift . lift

-- | Annotate the parser with a better error message.
(<?>) :: Monad m => EventParser l m a -> Text -> EventParser l m a
parser <?> msg = parser <|> throwError msg

-- | Parse a tag.  Parses the children in the order or the inner parser.
someTag :: (Monad (ItemM l), List l)
        => (Text -> Bool)
        -> AttrParser b
        -> (b -> EventParser l (ItemM l) a)
        -> EventParser l (ItemM l) a
someTag tagnameTest attrParser inner = EventParser $ do
  _ <- runEventParser skipToNextTag
  ParserState _ elems <- get
  case elems of
--  UnOrdered [] -> throwError "Unexpected end of input."
--  UnOrdered lst -> _ 
    Ordered Nil -> throwError "Unexpected end of input."
    Ordered (Cons (StartElement tagName attrs, loc) next)
      | tagnameTest tagName ->
          case runStateT (runAttrParser attrParser) attrs of
            Left err -> throwError err
            Right (attrData, []) -> do
              nextItem <- liftListT $ List.runList next
              put $ ParserState True (Ordered nextItem)
              runEventParser $ inner attrData
            Right (_, _attrs) -> throwError "unexpected attributes"            
    Ordered _ -> throwError "expected tag"
         
-- -- | 
-- someUnorderedTag  :: (Monad (ItemM l), List l)
--                   => (Text -> Bool)
--                   -> AttrParser b
--                   -> (b -> EventParser l (ItemM l) a)
--                   -> EventParser l (ItemM l) a
-- someUnorderedTag inner = _

-- | Skip next tag
skipTag :: (Monad (ItemM l), List l) => EventParser l (ItemM l) ()
skipTag = someTag (const True) skipAttrs $ const skipTags

-- | Skip remaining tags, if any.
skipTags :: (Monad (ItemM l), List l) => EventParser l (ItemM l) ()
skipTags = void $ many skipTag

-- | Skip zero or more tags until the given parser succeeds
skipTagsTill :: (Monad (ItemM l), List l)
             => EventParser l (ItemM l) a
             -> EventParser l (ItemM l) a
skipTagsTill = skipManyTill skipTag

-- | Parse a tag with the given name, using the inner parser for the
-- children tags.  The children tags are parsed in the order of the
-- inner parser.
tag :: (Monad (ItemM l), List l)
    => Text
    -> AttrParser b
    -> (b -> EventParser l (ItemM l) a)
    -> EventParser l (ItemM l) a
tag name = someTag (==name)

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
             => (Text -> Bool)
             -> AttrParser b
             -> EventParser l (ItemM l) b
someEmptyTag tagnameTest attrP = someTag tagnameTest attrP pure

-- | Parser a tag with the given name which can have no children.  If
-- the tag has children, an error is raised.
emptyTag :: (Monad (ItemM l), List l)
         => Text
         -> AttrParser b
         -> EventParser l (ItemM l) b
emptyTag name = someEmptyTag (==name)

-- | Parse text.  Note that parsing a tag will skip white space, so if
-- whitespace is significant, run this parser first.
text :: (Monad (ItemM l), List l)
     => EventParser l (ItemM l) Text
text = EventParser $ do
  ParserState consumed (Ordered firstItem) <- get
  let loop item texts = case item of
        Nil -> throwError "unexpected end of file"
        (Cons (eventTag, _) next) -> case eventTag of
          CharacterData textData -> do
            nextItem <- liftItemM $ List.runList next
            loop nextItem (textData:texts)
          StartElement _ _ -> pure (item, texts)
          EndElement _ -> pure (item, texts)
          FailDocument err -> throwError $ Text.pack $ show err
          _ -> do nextItem <- liftItemM $ List.runList next
                  loop nextItem []
  (lastList, texts) <- loop firstItem []
  put $ ParserState consumed (Ordered lastList)
  pure $ Text.concat $ reverse texts

