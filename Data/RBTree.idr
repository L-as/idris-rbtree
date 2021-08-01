||| Red black trees, adapted from Purely functional data structures by Chris Okasaki.
||| TODO: Implement insertion.
||| TODO: Implement deletion.
||| TODO: Prove that the correct values are fetched.
module Data.RBTree

import Data.Nat
import Data.DPair
import Data.List

data In : (a -> Bool) -> List a -> Type where
  MkIn : (x : a) -> (f x = True) -> (xs : List a) -> In f (x :: xs)
  MkInCons : (x : a) -> (xs : List a) -> In f xs -> In f (x :: xs)

getIn : In f (x::xs) -> Either (f x = True) (In f xs)
getIn (MkIn x p l) = Left p
getIn (MkInCons x xs p) = Right p

-- Why... https://github.com/idris-lang/Idris2/issues/1811
boolMatch : (x : Bool) -> Either (x = False) (x = True)
boolMatch False = Left Refl
boolMatch True = Right Refl

extractIn : (f : a -> Bool) -> (l : List a) -> (0 p : In f l) -> a
extractIn f (x::xs) p = case boolMatch (f x) of
  Right _ => x
  Left p2 =>
    let 0 p3 = case getIn p of {
      Left p4 => case replace {p = \x => x = True} p2 p4 of Refl impossible
      Right p5 => p5
    } in
    extractIn f xs p3 -- (?kkd (getIn p) p2)

inFilter : (f : a -> Bool) -> (l : List a) -> In f l -> In f (filter f l)
inFilter f [] p impossible
inFilter f (x :: xs) (MkIn x p xs) = rewrite p in MkIn x p (filter f xs)
inFilter f (x :: xs) (MkInCons x xs p) =
  let r = inFilter f xs p in
  case boolMatch (f x) of
    Left p' => rewrite p' in r
    Right p' => rewrite p' in MkInCons x (filter f xs) r

inFilter' : (f : a -> Bool) -> (g : a -> Bool) -> ((x : a) -> (g x = True) -> f x = True) -> (l : List a) -> In g l -> In g (filter f l)
inFilter' f g p1 [] p2 impossible
inFilter' f g p1 (x :: xs) (MkIn x p2 xs) =
  let p3 = p1 x p2 in
  rewrite p3 in MkIn x p2 (filter f xs) {f = g}
inFilter' f g p1 (x :: xs) (MkInCons x xs p2) =
  let r = inFilter' f g p1 xs p2 in
  case boolMatch (f x) of
    Left p3 => rewrite p3 in r
    Right p3 => rewrite p3 in MkInCons x (filter f xs) r

export
interface LawfulOrd a where
  compare : a -> a -> Ordering
  reflexive : (x : a) -> (compare x x = EQ)
  reversion : (x : a) -> (y : a) -> (compare x y = LT) -> (compare y x = GT)
  transitive : (x : a) -> (y : a) -> (z : a) -> (compare x y = LT) -> (compare y z = LT) -> (compare x z = LT)
  equality1 : (x : a) -> (y : a) -> (z : a) -> (compare x y = EQ) -> (compare x z = compare y z)
  equality2 : (x : a) -> (y : a) -> (z : a) -> (compare x y = EQ) -> (compare z x = compare z y)

(==) : LawfulOrd a => a -> a -> Bool
x == y = case compare x y of { EQ => True; _ => False }

(<) : LawfulOrd a => a -> a -> Bool
x < y = case compare x y of { LT => True; _ => False }

(>) : LawfulOrd a => a -> a -> Bool
x > y = case compare x y of { GT => True; _ => False }

convLT : LawfulOrd a => (x : a) -> (y : a) -> (x < y = True) -> (compare x y = LT)
convLT x y p with (compare x y)
  convLT x y Refl | GT impossible
  convLT x y Refl | EQ impossible
  convLT x y Refl | LT = Refl

convGT : LawfulOrd a => (x : a) -> (y : a) -> (x > y = True) -> (compare x y = GT)
convGT x y p with (compare x y)
  convGT x y Refl | GT = Refl
  convGT x y Refl | EQ impossible
  convGT x y Refl | LT impossible

convEQ : LawfulOrd a => (x : a) -> (y : a) -> (x == y = True) -> (compare x y = EQ)
convEQ x y p with (compare x y)
  convEQ x y Refl | GT impossible
  convEQ x y Refl | EQ = Refl
  convEQ x y Refl | LT impossible

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

data GoodTree : {height : Nat} -> {color : Color} -> {kt : Type} -> {kord : LawfulOrd kt} -> {keys : List kt} -> {vt : Type} -> Type where
  Empty : GoodTree {height = 0, color = Black, keys = []}
  RedNode : {0 kord : LawfulOrd kt} -> (k : kt) -> {0 kp : In (k ==) keys} -> vt -> GoodTree {height, color = Black, kt, kord, keys = filter (k >) keys, vt} -> GoodTree {height, color = Black, kt, kord, keys = filter (k <) keys, vt} -> GoodTree {height, color = Red, kt, kord, keys, vt}
  BlackNode : {0 kord : LawfulOrd kt} -> (k : kt) -> {0 kp : In (k ==) keys} -> vt -> GoodTree {height, kt, kord, keys = filter (k >) keys, vt} -> GoodTree {height, kt, kord, keys = filter (k <) keys, vt} -> GoodTree {height = S height, color = Black, kt, kord, keys, vt}

data OrderingEq : Ordering -> Type where
  LTEquality : (0 _ : x = LT) -> OrderingEq x
  EQEquality : (0 _ : x = EQ) -> OrderingEq x
  GTEquality : (0 _ : x = GT) -> OrderingEq x

-- Why... https://github.com/idris-lang/Idris2/issues/1811
orderingMatch : (x : Ordering) -> OrderingEq x
orderingMatch LT = LTEquality Refl
orderingMatch EQ = EQEquality Refl
orderingMatch GT = GTEquality Refl

index : {0 keys : List kt} -> {kord : LawfulOrd kt} -> (k : kt) -> {0 k_in_keys : In (k ==) keys} -> GoodTree {kt, kord, keys, vt} -> vt
index k Empty impossible
index k (RedNode k' v l r) = case orderingMatch (compare k' k) of
  EQEquality _ => v
  GTEquality p0 =>
    let 0 p1 = \x, p => helper k' k x (cong (\x => case x of {GT => True; _ => False}) p0) p in
    let 0 p2 : In (k ==) (filter (k' >) keys) = inFilter' (k' >) (k ==) p1 keys k_in_keys in
    index k l {k_in_keys = p2}
  LTEquality p0 =>
    let 0 p1 = \x, p => ( let p1' = replace {p = \arg => arg = LT} (equality2 k x k' (convEQ k x p)) p0 in let p1'' = cong (\arg => case arg of {LT => True; _ => False}) p1' in the (k' < x = True) p1'' ) in
    let 0 p2 : In (k ==) (filter (k' <) keys) = inFilter' (k' <) (k ==) p1 keys k_in_keys in
    index k r {k_in_keys = p2}
index k (BlackNode k' v l r) = case orderingMatch (compare k' k) of
  EQEquality _ => v
  GTEquality p0 =>
    let 0 p1 = \x, p => helper k' k x (cong (\x => case x of {GT => True; _ => False}) p0) p in
    let 0 p2 : In (k ==) (filter (k' >) keys) = inFilter' (k' >) (k ==) p1 keys k_in_keys in
    index k l {k_in_keys = p2}
  LTEquality p0 =>
    let 0 p1 = \x, p => ( let p1' = replace {p = \arg => arg = LT} (equality2 k x k' (convEQ k x p)) p0 in let p1'' = cong (\arg => case arg of {LT => True; _ => False}) p1' in the (k' < x = True) p1'' ) in
    let 0 p2 : In (k ==) (filter (k' <) keys) = inFilter' (k' <) (k ==) p1 keys k_in_keys in
    index k r {k_in_keys = p2}

{-
data BadTree : {height : Nat} -> {color : Color} -> {kt : Type} -> {kord : Ord kt} -> {keys : List kt} -> {vt : Type} -> Type where
  BadEmpty : BadTree {height = 0, color = Black, keys = []}
  BadRedNode : {0 kord : Ord kt} -> (k : kt) -> vt -> GoodTree {height, kt, kord, keys = keys1, vt} -> {0 proof1 : all (k <) keys1 = True} -> GoodTree {height, kt, kord, keys = keys2, vt} -> {0 proof2 : all (k >) keys2 = True} -> BadTree {height, color = Red, kt, kord, keys = k :: keys1 <+> keys2, vt}
  BadBlackNode : {0 kord : Ord kt} -> (k : kt) -> vt -> GoodTree {height, kt, kord, keys = keys1, vt} -> {0 proof1 : all (k <) keys1 = True} -> GoodTree {height, kt, kord, keys = keys2, vt} -> {0 proof2 : all (k >) keys2 = True} -> BadTree {height = S height, color = Black, kt, kord, keys = k :: keys1 <+> keys2, vt}
-}

{-
data GoodTree : {0 height : Nat} -> {0 color : Color} -> {0 kt : Type} -> {0 kord : Ord kt} -> {0 vt : Type} -> Type where
  Empty : GoodTree {height = 0, color = Black}
  RedNode : kt -> vt -> GoodTree {height, color = Black, kt, kord, vt} -> GoodTree {height, color = Black, kt, kord, vt} -> GoodTree {height, color = Red, kt, kord, vt}
  BlackNode : kt -> vt -> GoodTree {height, kt, kord, vt} -> GoodTree {height, kt, kord, vt} -> GoodTree {height = S height, color = Black, kt, kord, vt}

data BadTree : {0 height : Nat} -> {0 color : Color} -> {0 kt : Type} -> {0 kord : Ord kt} -> {0 vt : Type} -> Type where
  BadEmpty : BadTree {height = 0, color = Black}
  BadRedNode : kt -> vt -> GoodTree {height, kt, kord, vt} -> GoodTree {height, kt, kord, vt} -> BadTree {height, color = Red, kt, kord, vt}
  BadBlackNode : kt -> vt -> GoodTree {height, kt, kord, vt} -> GoodTree {height, kt, kord, vt} -> BadTree {height = S height, color = Black, kt, kord, vt}

balanceLeft : kt -> vt -> BadTree {height, kt, kord, vt} -> GoodTree {height, kt, kord, vt} -> Exists $ \color => GoodTree {height = S height, color, kt, kord, vt}
balanceLeft k v BadEmpty r = Evidence Black $ BlackNode k v Empty r
balanceLeft k v (BadBlackNode k' v' l' r') r = Evidence Black $ BlackNode k v (BlackNode k' v' l' r') r
balanceLeft zk zv (BadRedNode xk xv a (RedNode yk yv b c)) d = Evidence Red $ RedNode yk yv (BlackNode xk xv a b) (BlackNode zk zv c d)
balanceLeft zk zv (BadRedNode yk yv (RedNode xk xv a b) c) d = Evidence Red $ RedNode yk yv (BlackNode xk xv a b) (BlackNode zk zv c d)
balanceLeft xk xv (BadRedNode yk yv (BlackNode zk zv a b) (BlackNode wk wv c d)) e = Evidence Black $ BlackNode xk xv (RedNode yk yv (BlackNode zk zv a b) (BlackNode wk wv c d)) e
balanceLeft xk xv (BadRedNode yk yv Empty Empty) e = Evidence Black $ BlackNode xk xv (RedNode yk yv Empty Empty) e

mutual
  getf : (ko : Ord k) => k -> GoodTree n c k ko v -> Maybe v
  getf key node =
    case node of
      Empty => Nothing
      RedNode key' val l r => getf' key key' val l r
      BlackNode key' val l r => getf' key key' val l r

  getf' : (ko : Ord k) => k -> k -> v -> GoodTree n c1 k ko v -> GoodTree n c2 k ko v -> Maybe v
  getf' key key' val l r = case compare key key' of
    LT => getf key l
    EQ => Just val
    GT => getf key r

insertf' : (ko : Ord k) => k -> v -> GoodTree n1 c1 k ko v -> Exists (\n2 => Exists (\c2 => BadTree n2 c2 k ko v))
insertf' key val Empty = Evidence 1 $ Evidence Red (BadNode Red key val Empty Empty)
insertf' key val (RedNode key' val' l r) = ?dd
insertf' _ _ _ = ?inh

Functor (GoodTree n c) where
  map f Empty = Empty
  map f (RedNode x l r) = RedNode (f x) (f <$> l) (f <$> r)
  map f (BlackNode x l r) = BlackNode (f x) (f <$> l) (f <$> r)

export
data Tree : Type -> Type where
  MkTree : GoodTree height color a -> Tree a

export
empty : Tree a
empty = MkTree Empty
-}
