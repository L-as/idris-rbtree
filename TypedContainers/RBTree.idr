||| Red black trees, adapted from Purely functional data structures by Chris Okasaki.
|||
||| You are guaranteed to get the correct value for a key.
|||
||| TODO: Implement deletion.
|||
||| The code has a lot of duplication that can not be unduplicated in trivially
||| , due to the need to prove different things in different cases.

module TypedContainers.RBTree

import Data.Nat
import Data.DPair
import Data.List
import TypedContainers.In
import TypedContainers.LawfulOrd
import TypedContainers.RBTree.Base
import TypedContainers.RBTree.Index
import TypedContainers.RBTree.Insert


{-
export
data Tree : (kt : Type) -> (kord : LawfulOrd kt) => (kt -> Type) -> Type where
  MkTree : GoodTree {height, color, kt, kord, vt, keys} -> Tree kt vt {kord}

export
empty : LawfulOrd kt => Tree kt vt
empty = MkTree Empty

export
insert : LawfulOrd kt => (k : kt) -> vt k -> Tree kt vt -> Tree kt vt
insert = ?insertHole

export
index : LawfulOrd kt => kt -> Tree kt vt -> Maybe (Exists vt)
index = ?indexHole

export
index' : LawfullerOrd kt => (k : kt) -> Tree kt vt -> Maybe (vt k)
index' = ?index'Hole
-}
