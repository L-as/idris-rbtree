||| Red black trees, adapted from Purely functional data structures by Chris Okasaki.
|||
||| You are guaranteed to get the correct value for a key.
|||
||| TODO: Implement deletion.
|||
||| The code has a lot of duplication that can not be unduplicated in trivially
||| , due to the need to prove different things in different cases.

module Data.RBTree

import Data.Nat
import Data.DPair
import Data.List
import Data.In
import Data.LawfulOrd

-- TODO: Find out a way to do this without extensional function equality
0 funext : (f : a -> b) -> (g : a -> b) -> ((x : a) -> f x = g x) -> (f = g)
funext = funext

helper' : LawfulOrd a => (x : a) -> (y : a) -> (z : a) -> (compare x y = GT) -> (compare y z = EQ) -> (compare x z = GT)
helper' x y z p1 p2 = rewrite sym $ equality2 y z x p2 in p1

helper : LawfulOrd a => (x : a) -> (y : a) -> (z : a) -> (x > y = True) -> (y == z = True) -> (x > z = True)
helper x y z p1 p2 =
  let p1' = convGT x y p1 in
  let p2' = convEQ y z p2 in
  let p3 = equality2 y z x p2' in
  let p4 : (compare x z = GT) = replace {p = \arg => arg = GT} p3 p1' in
  cong (\case {GT => True; _ => False}) p4

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
toAlsoGoodTree : GoodTree {height, color, kt, kord, keys, vt} -> AlsoGoodTree {height, color, kt, kord, keys, vt}
toAlsoGoodTree Empty = AlsoEmpty
toAlsoGoodTree (BlackNode k v l r {kp}) = AlsoBlackNode k v l r {keyslEq = Refl, keysrEq = Refl, kp}
toAlsoGoodTree (RedNode k v l r {kp}) = AlsoRedNode k v l r {keyslEq = Refl, keysrEq = Refl, kp}

getColor : GoodTree {color} -> Subset Color (\color' => color = color')
getColor Empty = Element Black Refl
getColor (BlackNode _ _ _ _) = Element Black Refl
getColor (RedNode _ _ _ _) = Element Red Refl

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
    let 0 p1 = \x, p => helper k' k x (cong (\case {GT => True; _ => False}) p0) p in
    let 0 p2 : In (k ==) (filter (k' >) keys) = inFilter' (k' >) (k ==) p1 keys k_in_keys in
    indexG k l {k_in_keys = p2}
  LTEquality p0 =>
    let 0 p1 = \x, p => ( let p1' = replace {p = \arg => arg = LT} (equality2 k x k' (convEQ k x p)) p0 in let p1'' = cong (\case {LT => True; _ => False}) p1' in the (k' < x = True) p1'' ) in
    let 0 p2 : In (k ==) (filter (k' <) keys) = inFilter' (k' <) (k ==) p1 keys k_in_keys in
    indexG k r {k_in_keys = p2}
indexG k (BlackNode k' v l r) = case orderingMatch (compare k' k) of
  EQEquality p0 => Evidence k' $ Evidence p0 v
  GTEquality p0 =>
    let 0 p1 = \x, p => helper k' k x (cong (\case {GT => True; _ => False}) p0) p in
    let 0 p2 : In (k ==) (filter (k' >) keys) = inFilter' (k' >) (k ==) p1 keys k_in_keys in
    indexG k l {k_in_keys = p2}
  LTEquality p0 =>
    let 0 p1 = \x, p => ( let p1' = replace {p = \arg => arg = LT} (equality2 k x k' (convEQ k x p)) p0 in let p1'' = cong (\case {LT => True; _ => False}) p1' in the (k' < x = True) p1'' ) in
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

mutual
  insertLeftBlack :
    (kord : LawfulOrd kt) =>
    (k : kt) ->
    vt k ->
    (k' : kt) ->
    {0 kp : In (k' ==) keys} ->
    vt k' ->
    {0 ltEq : compare k k' = LT} ->
    {0 keyslEq : keysl = filter (k' >) keys} ->
    GoodTree {height, color = Black, kt, kord, keys = keysl, vt} ->
    {0 keysrEq : keysr = filter (k' <) keys} ->
    GoodTree {height, color = colorRight, kt, kord, keys = keysr, vt} ->
    (
      Exists \color' => GoodTree {color = color', height, kt, kord, vt, keys = filter (k' >) (k :: keys)},
      GoodTree {color = colorRight, height, kt, kord, vt, keys = filter (k' <) (k :: keys)}
    )
  insertLeftBlack k v k' v' l r =
    let (Evidence color' l') = insertG' k v (toAlsoGoodTree l) in
    let 0 p1 = reversion1 k k' ltEq in
    let 0 p2 = cong (\case { GT => True; _ => False }) p1 in
    let 0 p3 : (k :: filter (k' >) keys = filter (k' >) (k :: keys)) = rewrite p2 in Refl in
    let l'' : GoodTree {color = color', height, kt, kord, vt, keys = filter (k' >) (k :: keys)} =
      replace {p = \arg => GoodTree {height, color = color', kt, kord, vt, keys = arg}} p3 (rewrite sym keyslEq in l')
    in
    let 0 p4 : (k' < k = False) = cong (\case { LT => True; _ => False }) p1 in
    let 0 p5 : (filter (k' <) keys = filter (k' <) (k :: keys)) = rewrite p4 in Refl in
    let r' : GoodTree {color = colorRight, height, kt, kord, vt, keys = filter (k' <) (k :: keys)} =
      replace {p = \arg => GoodTree {height, color = colorRight, kt, kord, vt, keys = arg}} p5 (rewrite sym keysrEq in r)
    in
    (Evidence color' l'', r')

  insertBlackLeftBlack :
    (kord : LawfulOrd kt) =>
    (k : kt) ->
    vt k ->
    (k' : kt) ->
    {0 kp : In (k' ==) keys} ->
    vt k' ->
    {0 ltEq : compare k k' = LT} ->
    {0 keyslEq : keysl = filter (k' >) keys} ->
    GoodTree {height, color = Black, kt, kord, keys = keysl, vt} ->
    {0 keysrEq : keysr = filter (k' <) keys} ->
    GoodTree {height, color = colorRight, kt, kord, keys = keysr, vt} ->
    GoodTree {height = S height, color = Black, kt, kord, keys = k :: keys, vt}
  insertBlackLeftBlack k v k' v' l r =
    let (Evidence color' l', r') = insertLeftBlack k v k' v' l r {ltEq, keyslEq, keysrEq, kp} in
    BlackNode k' v' l' r' {kp = MkInCons k keys kp}

  insertBlackLeftRed :
    (kord : LawfulOrd kt) =>
    (k : kt) ->
    vt k ->
    (k' : kt) ->
    {0 kp : In (k' ==) keys} ->
    vt k' ->
    (0 ltEq : compare k k' = LT) ->
    {0 keyslEq : keysl = filter (k' >) keys} ->
    GoodTree {height, color = Red, kt, kord, keys = keysl, vt} ->
    {0 keysrEq : keysr = filter (k' <) keys} ->
    GoodTree {height, color = colorRight, kt, kord, keys = keysr, vt} ->
    Exists \color : Color => GoodTree {height = S height, color, kt, kord, keys = k :: keys, vt}
  insertBlackLeftRed = ?jjjedr

  insertG' :
    {0 color : Color} ->
    (kord : LawfulOrd kt) =>
    (k : kt) ->
    vt k ->
    AlsoGoodTree {kt, height, color, kord, vt, keys} ->
    case color of {
      Black => Exists {type = Color} \color : Color => GoodTree {height, color, kt, kord, vt, keys = k :: keys}
      Red => BadTree {height, kt, kord, vt, keys = k :: keys}
    }
  insertG' {keys = .([])} k v AlsoEmpty =
    let kp : (In (k ==) (k :: [])) = MkIn k (cong (\case {EQ => True; _ => False}) $ reflexivity k) [] in
    Evidence Red (
      RedNode k v
        (rewrite reflexivity k in Empty)
        (rewrite reflexivity k in Empty)
        {keys = k :: [], kp}
    )
  insertG' k v (AlsoRedNode k' v' l r {kp, keyslEq, keysrEq}) =
    case orderingMatch (compare k k') of
      LTEquality p0 =>
        let (Evidence color' l') = insertG' k v (toAlsoGoodTree l) in
        let 0 p1 = reversion1 k k' p0 in
        let 0 p2 = cong (\case { GT => True; _ => False }) p1 in
        let 0 p3 : (k :: filter (k' >) keys = filter (k' >) (k :: keys)) = rewrite p2 in Refl in
        let l'' : GoodTree {color = color', height, kt, kord, vt, keys = filter (k' >) (k :: keys)} =
          replace {p = \arg => GoodTree {height, color = color', kt, kord, vt, keys = arg}} p3 (rewrite sym keyslEq in l')
        in
        let 0 p4 : (k' < k = False) = cong (\case { LT => True; _ => False }) p1 in
        let 0 p5 : (filter (k' <) keys = filter (k' <) (k :: keys)) = rewrite p4 in Refl in
        let r' : GoodTree {color = Black, height, kt, kord, vt, keys = filter (k' <) (k :: keys)} =
          replace {p = \arg => GoodTree {height, color = Black, kt, kord, vt, keys = arg}} p5 (rewrite sym keysrEq in r)
        in
        BadRedNode k' v' l'' r' {kp = MkInCons k keys kp}
      EQEquality p0 =>
        let 0 p2 = funext (compare k') (compare k) (\x => equality1 k' k x (reversion3 k k' p0)) in
        -- Idris 2 parser is overly restrictive
        let 0 helper2 : ((f : Ordering -> Bool) -> {auto p1 : f EQ = False} -> (filter (\x => f (compare k' x)) keys = filter (\x => f (compare k x)) (k :: keys)))
            helper2 f {p1} =
              rewrite reflexivity k in
              rewrite p1 in
              cong (\arg => filter (\x => f (arg x)) keys) p2
        in
        let l' : GoodTree {color = Black, height, kt, kord, vt, keys = filter (k >) (k :: keys)} =
            replace {p = \arg => GoodTree {color = Black, height, kt, kord, vt, keys = arg}}
              (helper2 (\case { GT => True; _ => False }))
              (replace {p = \arg => GoodTree {height, color = Black, kt, kord, vt, keys = arg}} keyslEq l)
        in
        let r' : GoodTree {color = Black, height, kt, kord, vt, keys = filter (k <) (k :: keys)} =
            replace {p = \arg => GoodTree {color = Black, height, kt, kord, vt, keys = arg}}
              (helper2 (\case { LT => True; _ => False }))
              (replace {p = \arg => GoodTree {height, color = Black, kt, kord, vt, keys = arg}} keysrEq r)
        in
        BadRedNode k v l' r' {kp = MkIn k (cong (\case { EQ => True; _ => False }) (reflexivity k)) keys}
      GTEquality p0 =>
        let (Evidence color' r') = insertG' k v (toAlsoGoodTree r) in
        let 0 p1 = reversion2 k k' p0 in
        let 0 p2 = cong (\case { LT => True; _ => False }) p1 in
        let 0 p3 : (k :: filter (k' <) keys = filter (k' <) (k :: keys)) = rewrite p2 in Refl in
        let r'' : GoodTree {color = color', height, kt, kord, vt, keys = filter (k' <) (k :: keys)} =
          replace {p = \arg => GoodTree {height, color = color', kt, kord, vt, keys = arg}} p3 (rewrite sym keysrEq in r')
        in
        let 0 p4 : (k' > k = False) = cong (\case { GT => True; _ => False }) p1 in
        let 0 p5 : (filter (k' >) keys = filter (k' >) (k :: keys)) = rewrite p4 in Refl in
        let l' : GoodTree {color = Black, height, kt, kord, vt, keys = filter (k' >) (k :: keys)} =
          replace {p = \arg => GoodTree {height, color = Black, kt, kord, vt, keys = arg}} p5 (rewrite sym keyslEq in l)
        in
        BadRedNode k' v' l' r'' {kp = MkInCons k keys kp}
  insertG' k v whole@(AlsoBlackNode k' v' l r {kp, keysl, keyslEq, keysr, keysrEq, height = height'}) = case orderingMatch (compare k k') of
    LTEquality p0 =>
      case l of
        Empty => Evidence Black $ insertBlackLeftBlack k v k' v' l r {ltEq = p0, kp, keyslEq, keysrEq, kord, kt, vt, keysl, keysr, keys}
        (BlackNode _ _ _ _) => Evidence Black $ insertBlackLeftBlack k v k' v' l r {ltEq = p0, kp, keyslEq, keysrEq, kord, kt, vt, keysl, keysr, keys}
        (RedNode _ _ _ _) => insertBlackLeftRed k v k' v' p0 l r {kp, keyslEq, keysrEq, kord, kt, vt, keysl, keysr, keys}
    EQEquality p0 => ?heq
    GTEquality p0 => ?hgt
  insertG' _ _ _ = ?inshole

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
