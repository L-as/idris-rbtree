module TypedContainers.Util.Filter

import Data.List

%default total

public export
0 filterCommutative' :
  {f : a -> Bool} -> {g : a -> Bool} -> (xxs : List a) -> (yys : List a)
  -> (yys = filter f (filter g xxs)) -> (yys = filter g (filter f xxs))
filterCommutative' [] yys p = p
filterCommutative' (x :: xs) yys p =
  case the (DPair Bool (g x ===)) $ MkDPair (g x) Refl of
    MkDPair True p0 => case the (DPair Bool (f x ===)) $ MkDPair (f x) Refl of
      MkDPair True p1 =>
        let p2 : (filter f (x :: filter g xs) = filter f (filter g (x :: xs))) = rewrite p0 in Refl in
        let p3 : (x :: filter f (filter g xs) = filter f (x :: filter g xs)) = rewrite p1 in Refl in
        let p3 : (x :: filter f (filter g xs) = filter f (filter g (x :: xs))) = trans p3 p2 in
        case yys of
          [] impossible
          y :: ys =>
            let (Refl) : (y :: ys = x :: filter f (filter g xs)) = trans p (sym p3) in
            let p4 = filterCommutative' {f, g} xs ys Refl in
            rewrite p1 in rewrite p0 in cong (x ::) p4
      MkDPair False p1 =>
        let p2 : (filter f (x :: filter g xs) = filter f (filter g (x :: xs))) = rewrite p0 in Refl in
        let p3 : (filter f (filter g xs) = filter f (x :: filter g xs)) = rewrite p1 in Refl in
        let p3 : (filter f (filter g xs) = filter f (filter g (x :: xs))) = trans p3 p2 in
        case yys of
          [] impossible
          y :: ys =>
            let p4 : (y :: ys = filter f (filter g xs)) = trans p (sym p3) in
            let p5 = filterCommutative' {f, g} xs (y :: ys) p4 in
            rewrite p1 in p5
    MkDPair False p0 =>
      let p2 : (filter f (filter g (x :: xs)) = filter f (filter g xs)) = rewrite p0 in Refl in
      let p3 : (yys = filter f (filter g xs)) = trans p p2 in
      let p4 = filterCommutative' {f, g} xs yys p3 in
      case the (DPair Bool (f x ===)) $ MkDPair (f x) Refl of
        MkDPair True p5 => rewrite p5 in rewrite p0 in p4
        MkDPair False p5 => rewrite p5 in p4

public export
0 filterCommutative : (filter f (filter g l) = filter g (filter f l))
filterCommutative = filterCommutative' {f, g} l (filter f (filter g l)) Refl

0 filterImplication' :
  {f : a -> Bool} -> {g : a -> Bool}
  -> ((x : a) -> (g x = True) -> (f x = True)) -> (xxs : List a) -> (yys : List a)
  -> (yys = filter f (filter g xxs)) -> (yys = filter g xxs)
filterImplication' p0 [] yys p1 = p1
filterImplication' p0 (x :: xs) yys p1 =
  case the (DPair Bool (g x ===)) $ MkDPair (g x) Refl of
    MkDPair True p2 =>
      let p3 : (filter f (filter g (x :: xs)) = filter f (x :: filter g xs)) = rewrite p2 in Refl in
      let p4 : (filter f (x :: filter g xs) = x :: filter f (filter g xs)) = rewrite (p0 x p2) in Refl in
      let p5 : (yys = x :: filter f (filter g xs)) = trans (trans p1 p3) p4 in
      let p6 : (filter f (filter g xs) = filter g xs) = filterImplication' {f, g} p0 xs (filter f (filter g xs)) Refl in
      let p7 : (yys = x :: filter g xs) = replace {p = \p => yys === x :: p} p6 p5 in
      rewrite p2 in p7
    MkDPair False p2 =>
      let p3 : (filter f (filter g (x :: xs)) = filter f (filter g xs)) = rewrite p2 in Refl in
      let p5 : (yys = filter f (filter g xs)) = trans p1 p3 in
      let p6 : (filter f (filter g xs) = filter g xs) = filterImplication' {f, g} p0 xs (filter f (filter g xs)) Refl in
      let p7 : (yys = filter g xs) = replace {p = (yys ===)} p6 p5 in
      rewrite p2 in p7

public export
0 filterImplication : ((x : a) -> (g x = True) -> (f x = True)) -> (filter f (filter g l) = filter g l)
filterImplication p = filterImplication' {f, g} p l (filter f (filter g l)) Refl
