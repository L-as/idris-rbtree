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

%default total

export
data RBTree : (kt : Type) -> (kord : LawfulOrd kt) => (kt -> Type) -> Type where
  MkRBTree : GoodTree {height, color, kt, kord, vt, keys} -> RBTree kt vt {kord}

export
empty : LawfulOrd kt => RBTree kt vt
empty = MkRBTree (Empty Refl)

export
insert : LawfulOrd kt => (k : kt) -> vt k -> RBTree kt vt -> RBTree kt vt

export
index : LawfulOrd kt => kt -> RBTree kt vt -> Maybe (Exists vt)
--index k (MkRBTree tree) = indexG k tree

export
index' : LawfullerOrd kt => (k : kt) -> RBTree kt vt -> Maybe (vt k)
