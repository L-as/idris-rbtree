module TypedContainers.In

import Data.List
import Data.List.Elem
import Data.DPair

%default total

lemma0 : ([x] = [y]) -> (x = y)
lemma0 Refl = Refl

lemma1 : {0 xs : List a} -> {0 ys : List a} -> ((x :: xs) = (y :: ys)) -> (xs = ys)
lemma1 Refl = Refl

lemma2 : {0 xs : List a} -> {0 ys : List a} -> ((x :: xs) = (y :: ys)) -> (x = y)
lemma2 Refl = Refl

public export
data In : (a -> Bool) -> List a -> Type where
  MkIn : (x : a) -> (f x = True) -> (xs : List a) -> In f (x :: xs)
  MkInCons : (x : a) -> (0 xs : List a) -> In f xs -> In f (x :: xs)

public export
inFilter : (f : a -> Bool) -> (g : a -> Bool) -> ((x : a) -> (g x = True) -> f x = True) -> (l : List a) -> In g l -> In g (filter f l)
inFilter f g p1 [] p2 impossible
inFilter f g p1 (x :: xs) (MkIn x p2 xs) =
  let p3 = p1 x p2 in
  rewrite p3 in MkIn x p2 (filter f xs) {f = g}
inFilter f g p1 (x :: xs) (MkInCons x xs p2) =
  let r = inFilter f g p1 xs p2 in
  let MkDPair p2 p3 : DPair Bool (f x ===) = MkDPair (f x) Refl in
  case p2 of
    True => rewrite p3 in MkInCons x (filter f xs) r
    False => rewrite p3 in r

fromFilter : {f : a -> Bool} -> {l : List a} -> {lEq : l' === filter f l} -> Elem x l' -> (f x = True)
fromFilter (Here {x, xs}) = case l of
  [] impossible
  y :: ys =>
    let (MkDPair p0 p1) : DPair Bool ((f y) ===) = MkDPair (f y) Refl in
    case p0 of
      True =>
        let p2 : (y :: filter f ys = filter f (y :: ys)) = rewrite p1 in Refl in
        let p3 : (x :: xs = y :: filter f ys) = rewrite p2 in lEq in
        let p4 = lemma2 p3 in
        rewrite p4 in p1
      False =>
        let p2 : (filter f ys = filter f (y :: ys)) = rewrite p1 in Refl in
        let p3 : (x :: xs = filter f ys) = rewrite p2 in lEq in
        fromFilter {f, l = ys, lEq = p3} (Here {x, xs})
fromFilter (There p {x, y, xs}) =
  case l of
    [] impossible
    z :: zs =>
      let (MkDPair p0 p1) : DPair Bool ((f z) ===) = MkDPair (f z) Refl in
      case p0 of
        True =>
          let p2 : (z :: filter f zs = filter f (z :: zs)) = rewrite p1 in Refl in
          let p3 : (y :: xs = z :: filter f zs) = rewrite p2 in lEq in
          let p4 = lemma1 p3 in
          fromFilter {f, lEq = p4} p
        False =>
          let p2 : (filter f zs = filter f (z :: zs)) = rewrite p1 in Refl in
          let p3 : (y :: xs = filter f zs) = rewrite p2 in lEq in
          fromFilter {f, lEq = p3} (There p {x, y, xs})

extractIn' : {f : a -> Bool} -> {g : a -> Bool} -> {l : List a} -> {l' : List a} -> {lEq : l' = filter g l} -> In f l' -> DPair a (\x => (f x = True, g x = True))
extractIn' (MkIn x p0 xs) =
  let p1 = Here {x, xs} in
  let p2 = fromFilter {f = g, l, l' = x :: xs, lEq} p1 in
  MkDPair x (p0, p2)
extractIn' (MkInCons x xs rec) =
  case l of
    [] impossible
    y :: ys =>
      let (MkDPair p2 p3) : DPair Bool ((g y) ===) = MkDPair (g y) Refl in
      case p2 of
        True =>
          let p4 : (y :: filter g ys = filter g (y :: ys)) = rewrite p3 in Refl in
          let p5 : (x :: xs = y :: filter g ys) = rewrite p4 in lEq in
          extractIn' {f, g, l = ys, l' = xs, lEq = lemma1 p5} rec
        False =>
          let p4 : (filter g ys = filter g (y :: ys)) = rewrite p3 in Refl in
          let p5 : (x :: xs = filter g ys) = rewrite p4 in lEq in
          extractIn' {f, g, l = ys, l' = x :: xs, lEq = p5} (MkInCons x xs rec)

public export
extractIn : {f : a -> Bool} -> {g : a -> Bool} -> {l : List a} -> In f (filter g l) -> DPair a (\x => (f x = True, g x = True))
extractIn = extractIn' {lEq = Refl}

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
outFilter : {g : a -> Bool} -> {l : List a} -> In f (filter g l) -> In f l
outFilter p = outFilter' {f, g} l Refl p
