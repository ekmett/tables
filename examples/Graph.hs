{-# Language TemplateHaskell #-}
{-# Language TypeFamilies #-}
{-# Language GADTs #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language RankNTypes #-}
-- base
import Control.Applicative
-- containers
import Data.Set (Set)
import qualified Data.Set as S
-- lens
import Control.Lens
-- tables
import Data.Table

data Node = Node
  { _name :: Int
  , _arcs :: Set Int
  } deriving (Show)
makeLenses ''Node

instance Tabular Node where
  type PKT Node = Int
  data Key k Node b where
    Key  :: Key Primary Node Int
    Arcs :: Key Inverted Node (Set Int)
  data Tab Node i = NTab (i Primary Int)
    (i Inverted (Set Int))
  fetch Key = _name
  fetch Arcs = _arcs
  primary = Key
  primarily Key r = r
  mkTab f = NTab <$> f Key <*> f Arcs
  forTab (NTab i s) f = NTab <$> f Key i <*> f Arcs s
  ixTab (NTab i _) Key = i
  ixTab (NTab _ s) Arcs = s

main :: IO ()
main = do
  -- Make a lot of graph nodes.
  let t = fromList
        [ Node 1 (S.fromList [1, 2, 3])
        , Node 2 (S.fromList [1, 2, 3])
        , Node 3 (S.fromList [1, 2])
        , Node 4 (S.fromList [5])
        , Node 5 (S.fromList [4])
        , Node 6 (S.fromList [3])
        ]
  -- Print the names of all the nodes pointing to #3.
  print $ t ^.. withAny Arcs [3] . folded . name
  -- Print the names of all the nodes pointing to both #1 and #2.
  print $ t ^.. withAll Arcs [1, 2] . folded . name
