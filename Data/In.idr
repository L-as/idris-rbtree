module Data.In

import Data.List

public export
data In : (a -> Bool) -> List a -> Type where
  MkIn : (x : a) -> (f x = True) -> (xs : List a) -> In f (x :: xs)
  MkInCons : (x : a) -> (0 xs : List a) -> In f xs -> In f (x :: xs)

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

lemma0 : ([x] = [y]) -> (x = y)
lemma0 Refl = Refl

lemma1 : {0 xs : List a} -> {0 ys : List a} -> ((x :: xs) = (y :: ys)) -> (xs = ys)
lemma1 Refl = Refl

lemma2 : {0 xs : List a} -> {0 ys : List a} -> ((x :: xs) = (y :: ys)) -> (x = y)
lemma2 Refl = Refl

outFilter' : {0 f : a -> Bool} -> {g : a -> Bool} -> (xxs : List a) -> (pl : yys = filter g xxs) -> In f yys -> In f xxs
outFilter' [] pl (MkIn _ _ _) impossible
outFilter' [] pl (MkInCons _ _ _) impossible
outFilter' (x :: xs) pl (MkIn y py ys) with (g x)
  outFilter' (x :: xs) pl (MkIn y py ys) | True =
    let pl' = lemma2 pl in
    let px : (f x = True) = rewrite sym pl' in py in
    MkIn x px xs
  outFilter' (x :: xs) pl (MkIn y py ys) | False = MkInCons x xs $ outFilter' {f, g} xs pl (MkIn {f} y py ys)
outFilter' (x :: xs) pl (MkInCons y ys py) with (g x)
  outFilter' (x :: xs) pl (MkInCons y ys py) | True = MkInCons x xs $ outFilter' {f, g} xs (lemma1 pl) py
  outFilter' (x :: xs) pl (MkInCons y ys py) | False = MkInCons x xs $ outFilter' {f, g} xs pl (MkInCons y ys py)

public export
outFilter : {g : a -> Bool} -> (l : List a) -> In f (filter g l) -> In f l
outFilter l p = outFilter' {f, g} l Refl p
