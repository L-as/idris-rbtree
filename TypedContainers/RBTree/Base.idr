
module TypedContainers.RBTree.Base

import Data.List
import TypedContainers.In
import TypedContainers.LawfulOrd

public export
data Color = Red | Black

public export
data GoodTree :
  {height : Nat} ->
  {color : Color} ->
  {kt : Type} ->
  {kord : LawfulOrd kt} ->
  {keys : List kt} ->
  {vt : kt -> Type} -> Type
  where
  Empty : GoodTree {height = 0, color = Black, keys = []}
  RedNode :
    {0 kord : LawfulOrd kt} ->
    (k : kt) ->
    {0 kp : In (k ==) keys} ->
    vt k ->
    GoodTree {height, color = Black, kt, kord, keys = filter (k >) keys, vt} ->
    GoodTree {height, color = Black, kt, kord, keys = filter (k <) keys, vt} ->
    GoodTree {height, color = Red, kt, kord, keys, vt}
  BlackNode :
    {0 kord : LawfulOrd kt} ->
    (k : kt) ->
    {0 kp : In (k ==) keys} ->
    vt k ->
    GoodTree {height, kt, kord, keys = filter (k >) keys, vt} ->
    GoodTree {height, kt, kord, keys = filter (k <) keys, vt} ->
    GoodTree {height = S height, color = Black, kt, kord, keys, vt}

public export
data AlsoGoodTree :
  {height : Nat} ->
  {color : Color} ->
  {kt : Type} ->
  {kord : LawfulOrd kt} ->
  {keys : List kt} ->
  {vt : kt -> Type} -> Type
  where
  AlsoEmpty : AlsoGoodTree {height = 0, color = Black, keys = []}
  AlsoRedNode :
    {0 kord : LawfulOrd kt} ->
    (k : kt) ->
    {0 kp : In (k ==) keys} ->
    vt k ->
    {0 keyslEq : keysl = filter (k >) keys} ->
    GoodTree {height, color = Black, kt, kord, keys = keysl, vt} ->
    {0 keysrEq : keysr = filter (k <) keys} ->
    GoodTree {height, color = Black, kt, kord, keys = keysr, vt} ->
    AlsoGoodTree {height, color = Red, kt, kord, keys, vt}
  AlsoBlackNode :
    {0 kord : LawfulOrd kt} ->
    (k : kt) ->
    {0 kp : In (k ==) keys} ->
    vt k ->
    {0 keyslEq : keysl = filter (k >) keys} ->
    GoodTree {height, kt, kord, keys = keysl, vt} ->
    {0 keysrEq : keysr = filter (k <) keys} ->
    GoodTree {height, kt, kord, keys = keysr, vt} ->
    AlsoGoodTree {height = S height, color = Black, kt, kord, keys, vt}

-- TODO: Use new `id` optimization here https://github.com/idris-lang/Idris2/pull/1817
-- , which will require making AlsoGoodTree recursive on itself.
public export
toAlsoGoodTree : GoodTree {height, color, kt, kord, keys, vt} -> AlsoGoodTree {height, color, kt, kord, keys, vt}
toAlsoGoodTree Empty = AlsoEmpty
toAlsoGoodTree (BlackNode k v l r {kp}) = AlsoBlackNode k v l r {keyslEq = Refl, keysrEq = Refl, kp}
toAlsoGoodTree (RedNode k v l r {kp}) = AlsoRedNode k v l r {keyslEq = Refl, keysrEq = Refl, kp}

-- Like GoodTree but BadRedNode can have red children
public export
data BadTree :
  {height : Nat} ->
  {kt : Type} ->
  {kord : LawfulOrd kt} ->
  {keys : List kt} ->
  {vt : kt -> Type} -> Type
  where
  BadRedNode :
    {0 kord : LawfulOrd kt} ->
    (k : kt) ->
    {0 kp : In (k ==) keys} ->
    vt k ->
    GoodTree {height, kt, kord, keys = filter (k >) keys, vt} ->
    GoodTree {height, kt, kord, keys = filter (k <) keys, vt} ->
    BadTree {height, kt, kord, keys, vt}

