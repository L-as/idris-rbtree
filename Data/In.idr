module Data.In

import Data.List

public export
data In : (a -> Bool) -> List a -> Type where
  MkIn : (x : a) -> (f x = True) -> (xs : List a) -> In f (x :: xs)
  MkInCons : (x : a) -> (xs : List a) -> In f xs -> In f (x :: xs)

-- Why... https://github.com/idris-lang/Idris2/issues/1811
boolMatch : (x : Bool) -> Either (x = False) (x = True)
boolMatch False = Left Refl
boolMatch True = Right Refl

public export
inFilter : (f : a -> Bool) -> (l : List a) -> In f l -> In f (filter f l)
inFilter f [] p impossible
inFilter f (x :: xs) (MkIn x p xs) = rewrite p in MkIn x p (filter f xs)
inFilter f (x :: xs) (MkInCons x xs p) =
  let r = inFilter f xs p in
  case boolMatch (f x) of
    Left p' => rewrite p' in r
    Right p' => rewrite p' in MkInCons x (filter f xs) r

public export
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

--getIn : In f (x::xs) -> Either (f x = True) (In f xs)
--getIn (MkIn x p l) = Left p
--getIn (MkInCons x xs p) = Right p

--extractIn : (f : a -> Bool) -> (l : List a) -> (0 p : In f l) -> a
--extractIn f (x::xs) p = case boolMatch (f x) of
--  Right _ => x
--  Left p2 =>
--    let 0 p3 = case getIn p of {
--      Left p4 => case replace {p = \x => x = True} p2 p4 of Refl impossible
--      Right p5 => p5
--    } in
--    extractIn f xs p3 -- (?kkd (getIn p) p2)

