{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module Foo where

import Control.Applicative hiding (empty)
import Control.Lens
import Data.Data
import Data.Foldable as Foldable
import Data.Function (on)
import Data.Functor.Identity
import Data.List ((\\))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Table
import Data.Traversable
import qualified Prelude
import Prelude hiding (null)

-- * Example Table

data Foo a = Foo { fooId :: Int, fooBar :: a, fooBaz :: Double }
  deriving (Eq,Ord,Show,Read,Data,Typeable)

makeLensesWith ?? ''Foo $ defaultRules & lensField .~ \x -> Just (x ++ "_")

instance Tabular (Foo a) where
  type PKT (Foo a) = Int
  data Key k (Foo a) b where
    FooId  :: Key Primary   (Foo a) Int
    FooBaz :: Key Candidate (Foo a) Double
  data Tab (Foo a) i = FooTab (i Primary Int) (i Candidate Double)

  fetch FooId  = fooId
  fetch FooBaz = fooBaz

  primary = FooId
  primarily FooId r = r

  mkTab f               = FooTab <$> f FooId   <*> f FooBaz
  forTab (FooTab x y) f = FooTab <$> f FooId x <*> f FooBaz y
  ixTab (FooTab x _) FooId  = x
  ixTab (FooTab _ x) FooBaz = x

  autoTab = autoIncrement fooId_

test :: Table (Foo String)
test = [Foo 0 "One" 1.0, Foo 0 "Two" 2.0, Foo 0 "Three" 3.0, Foo 0 "Four" 4.0, Foo 0 "Five" 5.0]^.table
