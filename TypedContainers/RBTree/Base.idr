module TypedContainers.RBTree.Base

import Data.List
import TypedContainers.In
import TypedContainers.LawfulOrd

%default total

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
  Empty : (0 _ : keys = []) -> GoodTree {height = 0, color = Black, keys}
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
    GoodTree {height, color = colorLeft, kt, kord, keys = filter (k >) keys, vt} ->
    GoodTree {height, color = colorRight, kt, kord, keys = filter (k <) keys, vt} ->
    GoodTree {height = S height, color = Black, kt, kord, keys, vt}

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
