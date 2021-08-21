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

0 filterCommutative : (filter f (filter g l) = filter g (filter f l))
filterCommutative = filterCommutative' {f, g} l (filter f (filter g l)) Refl

0 filterImplication' :
  {f : a -> Bool} -> {g : a -> Bool}
  -> ((x : a) -> (f x = True) -> (g x = True)) -> (xxs : List a) -> (yys : List a)
  -> (yys = filter f (filter g xxs)) -> (yys = filter f l)

public export
0 filterImplication : ((x : a) -> (f x = True) -> (g x = True)) -> (filter f (filter g l) = filter f l)
filterImplication p = filterImplication' {f, g} p l (filter f (filter g l)) Refl
