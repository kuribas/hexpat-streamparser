{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Test.Hspec
import Text.XML.Expat.StreamParser
import Text.XML.Expat.SAX

main :: IO ()
main = hspec spec

spec :: Spec
spec =
  describe "parse XML tests" $ do
  it "skips tags" $
    parseXMLByteString (tag "foo" skipAttrs $ const skipTags)
    (ParseOptions Nothing Nothing) "<foo></foo>"
    `shouldBe` (Right () :: Either (EventParseError String, Maybe XMLParseLocation) ())

  
