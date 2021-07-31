||| Red black trees, adapted from Purely functional data structures by Chris Okasaki.
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

--any' : (a -> Bool) -> List a -> Bool
--any' f Nil = False
--any' f (x :: xs) = if f x then True else any' f xs

boolMatch : (x : Bool) -> Either (x = True) (x = False)
boolMatch True = Left Refl
boolMatch False = Right Refl

extractIn : (f : a -> Bool) -> (l : List a) -> (0 p : In f l) -> a
extractIn f (x::xs) p = case boolMatch (f x) of
	Left _ => x
	Right p2 =>
		let 0 p3 = case getIn p of {
			Left p4 => case replace {p = \x => x = True} p2 p4 of Refl impossible
			Right p5 => p5
		} in
		extractIn f xs p3 -- (?kkd (getIn p) p2)

transitiveIn : (f : a -> Bool) -> (g : a -> Bool) -> ((x : a) -> (g x = True) -> f x = True) -> (l : List a) -> In g l -> In f l
transitiveIn f g p1 l p2 = ?transitiveInHole

--inFilterHelper : (x : a) ->jk (p1 : f x = True) -> (p2 : In f xs)

filter' : (a -> Bool) -> List a -> List a
filter' f Nil = Nil
filter' f (x :: xs) = if f x then x :: filter' f xs else filter' f xs

inFilter : (f : a -> Bool) -> (l : List a) -> In f l -> In f (filter f l)
inFilter f [] p impossible
inFilter f (x :: xs) (MkIn x p xs) = rewrite p in MkIn x p (filter f xs)
inFilter f (x :: xs) (MkInCons x xs p) = the (In f (filter f (x :: xs))) ?haa
	--let r = inFilter f xs p in
  --the (In f (if f x then x :: filter f xs else filter f xs)) (?haa r)
	--case boolMatch (f x) of
	--	Left p' => ?haa $ MkInCons x (filter f xs) r
	--	Right p' => ?hac r
inFilter f l p = ?hab

helper : (f : a -> Bool) -> (g : a -> Bool) -> ((x : a) -> (g x = True) -> f x = True) -> (l : List a) -> In g l -> In g (filter f l)
helper f g p1 l p2 = ?helperHole

eq' : Ord a => a -> a -> Bool
eq' x y = case compare x y of
	EQ => True
	_ => False

lt' : Ord a => a -> a -> Bool
lt' x y = case compare x y of
	LT => True
	_ => False

gt' : Ord a => a -> a -> Bool
gt' x y = case compare x y of
	GT => True
	_ => False

data Color = Red | Black

data GoodTree : {height : Nat} -> {color : Color} -> {kt : Type} -> {kord : Ord kt} -> {keys : List kt} -> {vt : Type} -> Type where
	Empty : GoodTree {height = 0, color = Black, keys = []}
	RedNode : {0 kord : Ord kt} -> (k : kt) -> {0 kp : In (k `eq'`) keys} -> vt -> GoodTree {height, color = Black, kt, kord, keys = filter (k `lt'`) keys, vt} -> GoodTree {height, color = Black, kt, kord, keys = filter (k `gt'`) keys, vt} -> GoodTree {height, color = Red, kt, kord, keys, vt}
	BlackNode : {0 kord : Ord kt} -> (k : kt) -> {0 kp : In (k `eq'`) keys} -> vt -> GoodTree {height, kt, kord, keys = filter (k `lt'`) keys, vt} -> GoodTree {height, kt, kord, keys = filter (k `gt'`) keys, vt} -> GoodTree {height = S height, color = Black, kt, kord, keys, vt}

index : {0 keys : List kt} -> {kord : Ord kt} -> (k : kt) -> {0 k_in_keys : In (k `eq'`) keys} -> GoodTree {kt, kord, keys, vt} -> vt
index k Empty impossible
index k (RedNode k' v l r) = case compare k k' of
	EQ => v
	LT =>
	  let 0 p : In (k `eq'`) (filter (k' `lt'`) keys) = helper (k' `lt'`) (k `eq'`) ?hha keys k_in_keys in
    index k l {k_in_keys = p}
	GT =>
	  let 0 p : In (k `eq'`) (filter (k' `gt'`) keys) = helper (k' `gt'`) (k `eq'`) ?hhb keys k_in_keys in
    index k r {k_in_keys = p}
index _ _ = ?indexHole

--index : {kord : Ord kt} -> {0 keys : List kt} -> (k : kt) -> {0 k_in_keys : elem k keys = True} -> GoodTree {kt, kord, keys, vt} -> vt
--index k (RedNode k' v l r) = case compare k k' of
--	LT => index k l
--	EQ => v
--	GT => index k r
--index _ _ = ?indexhole

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
