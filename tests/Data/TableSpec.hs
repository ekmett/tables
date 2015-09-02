{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Data.TableSpec where

import Control.Lens
import Data.Table
import Test.Hspec


data Foo = Foo { _k :: String, _v :: String }
  deriving (Eq, Ord, Show, Read)

makeLenses ''Foo

instance Tabular Foo where
  type PKT Foo = String
  data Key k Foo a where
    FooK :: Key Primary Foo String
    FooV :: Key Supplemental Foo String
  data Tab Foo i = FooTab (i Primary String)
                          (i Supplemental String)

  fetch FooK = _k
  fetch FooV = _v

  primary = FooK
  primarily FooK r = r

  mkTab f               = FooTab <$> f FooK   <*> f FooV
  forTab (FooTab a b) f = FooTab <$> f FooK a <*> f FooV b
  ixTab (FooTab a _) FooK = a
  ixTab (FooTab _ b) FooV = b


tableA, tableB, tableC, tableD, tableE, tableF, tableG, tableH, tableI,
 tableA', tableB', tableC', tableD', tableE', tableF', tableG', tableH', tableI' :: Table Foo

tableA = fromList [Foo "a" "A", Foo "b" "hello"]
tableA' = fromList [Foo {_k = "a", _v = "A"}, Foo {_k = "b", _v = "hello"}]

tableB = insert (Foo "a" "Y") tableA
tableB' = fromList [Foo {_k = "a", _v = "Y"}, Foo {_k = "b", _v = "hello"}]

tableC = tableB ^. with FooV (/=) ""
tableC' = fromList [Foo {_k = "a", _v = "Y"}, Foo {_k = "b", _v = "hello"}]

tableD = (tableA & ix "a" . v .~ "OH! NO!") ^. with FooV (/=) ""
tableD' = fromList [Foo {_k = "a", _v = "OH! NO!"}, Foo {_k = "b", _v = "hello"}]

tableE = tableC ^. with FooV (/=) ""
tableE' = fromList [Foo {_k = "a", _v = "Y"}, Foo {_k = "b", _v = "hello"}]

tableF = tableC ^. with _v (==) "A"
tableF' = fromList []

tableG = tableC ^. with _v (==) "Y"
tableG' = fromList [Foo {_k = "a", _v = "Y"}]

tableH = tableC ^. with FooV (==) "Y"
tableH' = fromList [Foo {_k = "a", _v = "Y"}]

tableI = tableC ^. with _v (==) "Y"
tableI' = fromList [Foo {_k = "a", _v = "Y"}]


tests :: IO ()
tests = hspec spec

spec :: Spec
spec = describe "Data.Table" . it "unit tests" $ do
  mapM_ (\ (i :: String, t, t') -> (i, t) `shouldBe` (i, t'))
    [ ("A", tableA, tableA')
    , ("B", tableB, tableB')
    , ("C", tableC, tableC')
    , ("E", tableE, tableE')
    , ("F", tableF, tableF')
    , ("G", tableG, tableG')
    , ("H", tableH, tableH')
    , ("I", tableI, tableI')
    , ("D", tableD, tableD')
    ]
