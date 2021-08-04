||| Red black trees, adapted from Purely functional data structures by Chris Okasaki.
|||
||| You are guaranteed to get the correct value for a key.
|||
||| TODO: Implement insertion.
||| TODO: Implement deletion.
module Data.RBTree

import Data.Nat
import Data.DPair
import Data.List
import Data.In
import Data.LawfulOrd

xj : (f : a -> b) -> (g : a -> b) -> ((x : a) -> f x = g x) -> ((\x => f x) = (\x => g x))
xj f g p = ?xjh

helper' : LawfulOrd a => (x : a) -> (y : a) -> (z : a) -> (compare x y = GT) -> (compare y z = EQ) -> (compare x z = GT)
helper' x y z p1 p2 = rewrite sym $ equality2 y z x p2 in p1

helper : LawfulOrd a => (x : a) -> (y : a) -> (z : a) -> (x > y = True) -> (y == z = True) -> (x > z = True)
helper x y z p1 p2 =
  let p1' = convGT x y p1 in
  let p2' = convEQ y z p2 in
  let p3 = equality2 y z x p2' in
  let p4 : (compare x z = GT) = replace {p = \arg => arg = GT} p3 p1' in
  cong (\arg => case arg of {GT => True; _ => False}) p4

data Color = Red | Black

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

data OrderingEq : Ordering -> Type where
  LTEquality : (0 _ : x === LT) -> OrderingEq x
  EQEquality : (0 _ : x === EQ) -> OrderingEq x
  GTEquality : (0 _ : x === GT) -> OrderingEq x

-- Why... https://github.com/idris-lang/Idris2/issues/1811
orderingMatch : (x : Ordering) -> OrderingEq x
orderingMatch LT = LTEquality Refl
orderingMatch EQ = EQEquality Refl
orderingMatch GT = GTEquality Refl

indexG : {0 keys : List kt} -> {kord : LawfulOrd kt} -> (k : kt) -> {0 k_in_keys : In (k ==) keys} -> GoodTree {kt, kord, keys, vt} -> Exists $ \k' => Exists $ \_ : compare k' k = EQ => vt k'
indexG k Empty impossible
indexG k (RedNode k' v l r) = case orderingMatch (compare k' k) of
  EQEquality p0 => Evidence k' $ Evidence p0 v
  GTEquality p0 =>
    let 0 p1 = \x, p => helper k' k x (cong (\x => case x of {GT => True; _ => False}) p0) p in
    let 0 p2 : In (k ==) (filter (k' >) keys) = inFilter' (k' >) (k ==) p1 keys k_in_keys in
    indexG k l {k_in_keys = p2}
  LTEquality p0 =>
    let 0 p1 = \x, p => ( let p1' = replace {p = \arg => arg = LT} (equality2 k x k' (convEQ k x p)) p0 in let p1'' = cong (\arg => case arg of {LT => True; _ => False}) p1' in the (k' < x = True) p1'' ) in
    let 0 p2 : In (k ==) (filter (k' <) keys) = inFilter' (k' <) (k ==) p1 keys k_in_keys in
    indexG k r {k_in_keys = p2}
indexG k (BlackNode k' v l r) = case orderingMatch (compare k' k) of
  EQEquality p0 => Evidence k' $ Evidence p0 v
  GTEquality p0 =>
    let 0 p1 = \x, p => helper k' k x (cong (\x => case x of {GT => True; _ => False}) p0) p in
    let 0 p2 : In (k ==) (filter (k' >) keys) = inFilter' (k' >) (k ==) p1 keys k_in_keys in
    indexG k l {k_in_keys = p2}
  LTEquality p0 =>
    let 0 p1 = \x, p => ( let p1' = replace {p = \arg => arg = LT} (equality2 k x k' (convEQ k x p)) p0 in let p1'' = cong (\arg => case arg of {LT => True; _ => False}) p1' in the (k' < x = True) p1'' ) in
    let 0 p2 : In (k ==) (filter (k' <) keys) = inFilter' (k' <) (k ==) p1 keys k_in_keys in
    indexG k r {k_in_keys = p2}

-- Like GoodTree but BadRedNode can have red children
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

{-
constructBlack :
  (kord : LawfulOrd kt) =>
  (k : kt) ->
  vt k ->
  GoodTree {height, kt, kord, vt, keys = keysl} ->
  {0 pl : all (Data.RBTree.(>) k) keysl = True} ->
  GoodTree {height, kt, kord, vt, keys = keysr} ->
  {0 pr : all (Data.RBTree.(<) k) keysr = True} ->
  GoodTree {height = S height, color = Black, kt, kord, vt, keys = keysl <+> (k :: keysr)}
constructBlack = ?constructBlackHole

balanceLeft :
  (kord : LawfulOrd kt) =>
  (k : kt) ->
  vt k ->
  BadTree {height, kt, kord, vt, keys = keysl} ->
  {0 pl : all (Data.RBTree.(>) k) keysl = True} ->
  GoodTree {height, kt, kord, vt, keys = keysr} ->
  {0 pr : all (Data.RBTree.(<) k) keysr = True} ->
  Exists $ \color => GoodTree {height = S height, color, kt, kord, vt, keys = keysl <+> (k :: keysr)}
balanceLeft {keysl = .([])} k v BadEmpty r = Evidence Black $ constructBlack k v Empty r {keysl = [], keysr, pl, pr}
--balanceLeft k v (BadBlackNode k' v' l' r') r = Evidence Black $ BlackNode k v (BlackNode k' v' l' r' {keys = _}) r
--balanceLeft zk zv (BadRedNode xk xv a (RedNode yk yv b c)) d = Evidence Red $ RedNode yk yv (BlackNode xk xv a b) (BlackNode zk zv c d)
--balanceLeft zk zv (BadRedNode yk yv (RedNode xk xv a b) c) d = Evidence Red $ RedNode yk yv (BlackNode xk xv a b) (BlackNode zk zv c d)
--balanceLeft xk xv (BadRedNode yk yv (BlackNode zk zv a b) (BlackNode wk wv c d)) e = Evidence Black $ BlackNode xk xv (RedNode yk yv (BlackNode zk zv a b) (BlackNode wk wv c d)) e
--balanceLeft xk xv (BadRedNode yk yv Empty Empty) e = Evidence Black $ BlackNode xk xv (RedNode yk yv Empty Empty) e
balanceLeft _ _ _ _ = ?balanceLeftHole
-}

insertG' :
  {0 color : Color} ->
  (kord : LawfulOrd kt) =>
  (k : kt) ->
  vt k ->
  GoodTree {kt, height, color, kord, vt, keys} ->
  case color of {
    Black => Exists \color => GoodTree {height, color, kt, kord, vt, keys = k :: keys}
    Red => BadTree {height, kt, kord, vt, keys = k :: keys}
  }
insertG' {keys = .([])} k v Empty =
  let kp : (In (k ==) (k :: [])) = MkIn k (cong (\arg => case arg of {EQ => True; _ => False}) $ reflexivity k) [] in
  Evidence Red (
    RedNode k v
      (rewrite reflexivity k in Empty)
      (rewrite reflexivity k in Empty)
      {keys = k :: [], kp}
  )
insertG' k v (RedNode k' v' l r {kp}) =
  case orderingMatch (compare k k') of
    LTEquality p0 =>
      let (Evidence color' l') = insertG' k v l in
      let 0 p1 = reversion1 k k' p0 in
      let 0 p2 = cong (\arg => case arg of { GT => True; _ => False }) p1 in
      let 0 p3 : (k :: filter (k' >) keys = filter (k' >) (k :: keys)) = rewrite p2 in Refl in
      let l'' : GoodTree {color = color', height, kt, kord, vt, keys = filter (k' >) (k :: keys)} =
        replace {p = \arg => GoodTree {height, color = color', kt, kord, vt, keys = arg}} p3 l'
      in
      let 0 p4 : (k' < k = False) = cong (\arg => case arg of { LT => True; _ => False }) p1 in
      let 0 p5 : (filter (k' <) keys = filter (k' <) (k :: keys)) = rewrite p4 in Refl in
      let r' : GoodTree {color = Black, height, kt, kord, vt, keys = filter (k' <) (k :: keys)} =
        replace {p = \arg => GoodTree {height, color = Black, kt, kord, vt, keys = arg}} p5 r
      in
      BadRedNode k' v' l'' r' {kp = MkInCons k keys kp}
    EQEquality p0 =>
      -- Idris 2 parser is overly restrictive
      let helper2 : ((f : Ordering -> Bool) -> {auto p1 : f EQ = False} -> (filter (\x => f (compare k' x)) keys = filter (\x => f (compare k x)) (k :: keys)))
          helper2 f {p1} = rewrite reflexivity k in rewrite p1 in ?huhu Refl
      in
      let l' : GoodTree {color = Black, height, kt, kord, vt, keys = filter (k >) (k :: keys)} =
          replace {p = \arg => GoodTree {color = Black, height, kt, kord, vt, keys = arg}}
            (helper2 (\x => case x of { GT => True; _ => False }))
            l
      in
      let r' : GoodTree {color = Black, height, kt, kord, vt, keys = filter (k <) (k :: keys)} =
          replace {p = \arg => GoodTree {color = Black, height, kt, kord, vt, keys = arg}}
            (helper2 (\x => case x of { LT => True; _ => False }))
            r
      in
      BadRedNode k v l' r' {kp = MkIn k (cong (\arg => case arg of { EQ => True; _ => False }) (reflexivity k)) keys}
    GTEquality p0 =>
      let (Evidence color' r') = insertG' k v r in
      let 0 p1 = reversion2 k k' p0 in
      let 0 p2 = cong (\arg => case arg of { LT => True; _ => False }) p1 in
      let 0 p3 : (k :: filter (k' <) keys = filter (k' <) (k :: keys)) = rewrite p2 in Refl in
      let r'' : GoodTree {color = color', height, kt, kord, vt, keys = filter (k' <) (k :: keys)} =
        replace {p = \arg => GoodTree {height, color = color', kt, kord, vt, keys = arg}} p3 r'
      in
      let 0 p4 : (k' > k = False) = cong (\arg => case arg of { GT => True; _ => False }) p1 in
      let 0 p5 : (filter (k' >) keys = filter (k' >) (k :: keys)) = rewrite p4 in Refl in
      let l' : GoodTree {color = Black, height, kt, kord, vt, keys = filter (k' >) (k :: keys)} =
        replace {p = \arg => GoodTree {height, color = Black, kt, kord, vt, keys = arg}} p5 l
      in
      BadRedNode k' v' l' r'' {kp = MkInCons k keys kp}
insertG' _ _ _ = ?insertG'Hole

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
