module TypedContainers.RBTree.Insert

import Data.Nat
import Data.DPair
import Data.List
import TypedContainers.In
import TypedContainers.LawfulOrd
import TypedContainers.RBTree.Base
import TypedContainers.Util.Filter

%default total

-- TODO: Find out a way to do this without extensional function equality
partial
0 funext : (f : a -> b) -> (g : a -> b) -> ((x : a) -> f x = g x) -> (f = g)
funext = funext

GoodBadTree :
  {height : Nat} ->
  {kt : Type} ->
  {kord : LawfulOrd kt} ->
  {keys : List kt} ->
  {vt : kt -> Type} ->
  Color ->
  Type
GoodBadTree c = case c of
  Black => Exists \color' => GoodTree {color = color', height, kt, kord, vt, keys}
  Red => BadTree {height, kt, kord, vt, keys}

0 lemma0 : LawfulOrd kt => {keys : List kt} -> (xk : kt) -> (yk : kt) -> In (yk ==) (filter (xk <) keys) -> (compare xk yk = LT)
lemma0 xk yk p0 =
  let MkDPair v (p3, p4) = extractIn p0 in
  let p5 = equality2 _ _ xk (convEQ _ _ p3) in
  let p6 = convLT xk v p4 in
  trans p5 p6

0 lemma1 : LawfulOrd kt => {keys : List kt} -> (xk : kt) -> (yk : kt) -> In (yk ==) (filter (xk >) keys) -> (compare xk yk = GT)
lemma1 xk yk p0 =
  let MkDPair v (p3, p4) = extractIn p0 in
  let p5 = equality2 _ _ xk (convEQ _ _ p3) in
  let p6 = convGT xk v p4 in
  trans p5 p6

balanceLeft :
  (kord : LawfulOrd kt) =>
  (zk : kt) ->
  {0 zkp : In (zk ==) keys} ->
  vt zk ->
  BadTree {height, kt, kord, keys = filter (zk >) keys, vt} ->
  GoodTree {height, color = colorRight, kt, kord, keys = filter (zk <) keys, vt} ->
  Exists \color : Color => GoodTree {height = S height, color, kt, kord, keys = keys, vt}
balanceLeft zk zv (BadRedNode {kp = xkp} xk xv a (RedNode yk yv b c {kp = ykp})) d =
  let
    0 p0 : (arg : kt) -> (xk == arg = True) -> (yk > arg = True)
    p0 arg prr =
      let pp0 = reversion1 xk yk $ lemma0 xk yk ykp in
      let pp1 = equality2 xk arg yk (convEQ xk arg prr) in
      let pp2 = trans (sym pp1) pp0 in
      cong (\case { GT => True; _ => False }) pp2

    0 p0' : (arg : kt) -> (zk == arg = True) -> (yk < arg = True)
    p0' arg prr =
      let pp0 = lemma1 zk yk (outFilter ykp) in
      let pp1 = equality1 zk arg yk (convEQ zk arg prr) in
      let pp2 = trans (sym pp1) pp0 in
      cong (\case { LT => True; _ => False }) $ reversion2 arg yk pp2

    0 p1 : (arg : kt) -> (xk > arg = True) -> (yk > arg = True)
    p1 arg pp0 =
      let pp1 : (compare arg xk = LT) = reversion2 xk arg $ convGT _ _ pp0 in
      let pp2 : (compare xk yk = LT) = lemma0 xk yk ykp in
      let pp3 : (compare arg yk = LT) = transitivity arg xk yk pp1 pp2 in
      cong (\case { GT => True; _ => False }) $ reversion1 arg yk pp3

    0 p1' : (arg : kt) -> (yk < arg = True) -> (xk < arg = True)
    p1' arg pp0 =
      let pp1 : (compare yk arg = LT) = convLT _ _ pp0 in
      let pp2 : (compare xk arg = LT) = transitivity xk yk arg (lemma0 xk yk ykp) pp1 in
      cong (\case { LT => True; _ => False }) pp2

    0 p2 : (arg : kt) -> (yk > arg = True) -> (zk > arg = True)
    p2 arg pp0 =
      let pp1 : (compare arg yk = LT) = reversion2 yk arg $ convGT _ _ pp0 in
      let pp2 : (compare yk zk = LT) = reversion2 zk yk $ lemma1 zk yk (outFilter ykp) in
      let pp3 : (compare arg zk = LT) = transitivity arg yk zk pp1 pp2 in
      cong (\case { GT => True; _ => False }) $ reversion1 arg zk pp3

    0 p2' : (arg : kt) -> (zk < arg = True) -> (yk < arg = True)
    p2' arg pp0 =
      let pp1 : (compare zk arg = LT) = convLT _ _ pp0 in
      let pp2 : (compare yk arg = LT) = transitivity yk zk arg (reversion2 zk yk $ lemma1 zk yk (outFilter ykp)) pp1 in
      cong (\case { LT => True; _ => False }) pp2

    0 p3 : ((filter (xk >) $ filter (zk >) keys) === (filter (xk >) $ filter (yk >) keys))
    p3 =
      let pp0 : ((filter (yk >) $ filter (xk >) $ filter (zk >) keys) === (filter (xk >) $ filter (zk >) keys))
          = filterImplication {g = (xk >), f = (yk >)} p1
      in
      let pp1 : ((filter (xk >) $ filter (yk >) $ filter (zk >) keys) === (filter (yk >) $ filter (xk >) $ filter (zk >) keys))
          = filterCommutative
      in
      let pp2 : ((filter (xk >) $ filter (zk >) $ filter (yk >) keys) === (filter (xk >) $ filter (yk >) $ filter (zk >) keys))
          = cong (filter (xk >)) filterCommutative
      in
      let pp3 : ((filter (xk >) $ filter (yk >) keys) === (filter (xk >) $ filter (zk >) $ filter (yk >) keys))
          = cong (filter (xk >)) $ sym $ filterImplication p2
      in
      sym $ trans pp3 $ trans pp2 $ trans pp1 pp0

    0 p4 : ((filter (yk >) $ filter (xk <) $ filter (zk >) keys) === (filter (xk <) $ filter (yk >) keys))
    p4 =
      let pp0 : ((filter (xk <) $ filter (yk >) $ filter (zk >) keys) === (filter (yk >) $ filter (xk <) $ filter (zk >) keys))
          = filterCommutative
      in
      let pp1 : ((filter (xk <) $ filter (zk >) $ filter (yk >) keys) === (filter (xk <) $ filter (yk >) $ filter (zk >) keys))
          = cong (filter (xk <)) filterCommutative
      in
      let pp2 : ((filter (xk <) $ filter (yk >) keys) === (filter (xk <) $ filter (zk >) $ filter (yk >) keys))
          = cong (filter (xk <)) $ sym $ filterImplication p2
      in
      sym $ trans pp2 $ trans pp1 pp0

    0 p5 : ((filter (yk <) $ filter (xk <) $ filter (zk >) keys) === (filter (zk >) $ filter (yk <) keys))
    p5 =
      let pp0 : ((filter (xk <) $ filter (yk <) $ filter (zk >) keys) === (filter (yk <) $ filter (xk <) $ filter (zk >) keys))
          = filterCommutative
      in
      let pp1 : ((filter (yk <) $ filter (zk >) keys) === (filter (xk <) $ filter (yk <) $ filter (zk >) keys))
          = sym $ filterImplication p1'
      in
      let pp2 : ((filter (zk >) $ filter (yk <) keys) === (filter (yk <) $ filter (zk >) keys))
          = filterCommutative
      in
      sym $ trans pp2 $ trans pp1 pp0

    0 p6 : (filter (zk <) keys) === (filter (zk <) $ filter (yk <) keys)
    p6 =
      let pp0 : ((filter (yk <) $ filter (zk <) keys) === (filter (zk <) keys))
          = filterImplication p2'
      in
      let pp1 : ((filter (zk <) $ filter (yk <) keys) === (filter (yk <) $ filter (zk <) keys))
          = filterCommutative
      in
      sym $ trans pp1 pp0
  in
  let a' : GoodTree {keys = filter (xk >) $ filter (yk >) keys} = rewrite sym p3 in a in
  let b' : GoodTree {keys = filter (xk <) $ filter (yk >) keys} = rewrite sym p4 in b in
  let c' : GoodTree {keys = filter (zk >) $ filter (yk <) keys} = rewrite sym p5 in c in
  let d' : GoodTree {keys = filter (zk <) $ filter (yk <) keys} = rewrite sym p6 in d in
  let l' = BlackNode xk xv a' b' {kp = inFilter (yk >) (xk ==) p0 _ (outFilter xkp)} in
  let r' = BlackNode zk zv c' d' {kp = inFilter (yk <) (zk ==) p0' _ zkp} in
  Evidence Red $ RedNode yk yv l' r' {kp = outFilter $ outFilter ykp}
balanceLeft zk zv (BadRedNode {kp = ykp} yk yv (RedNode xk xv a b {kp = xkp}) c) d =
  let
    0 p0 : (arg : kt) -> (zk == arg = True) -> (yk < arg = True)
    p0 arg prr =
      let pp0 = lemma1 zk yk ykp in
      let pp1 = equality1 zk arg yk (convEQ zk arg prr) in
      let pp2 = trans (sym pp1) pp0 in
      cong (\case { LT => True; _ => False }) $ reversion2 arg yk pp2

    0 p1 : (In (xk ==) (filter (yk >) keys))
    p1 = outFilter $ replace {p = In (xk ==)} filterCommutative xkp

    0 p2 : (arg : kt) -> (yk > arg = True) -> (zk > arg = True)
    p2 arg pp0 =
      let pp1 : (compare arg yk = LT) = reversion2 yk arg $ convGT _ _ pp0 in
      let pp2 : (compare yk zk = LT) = reversion2 zk yk $ lemma1 zk yk ykp in
      let pp3 : (compare arg zk = LT) = transitivity arg yk zk pp1 pp2 in
      cong (\case { GT => True; _ => False }) $ reversion1 arg zk pp3

    0 p2' : (arg : kt) -> (zk < arg = True) -> (yk < arg = True)
    p2' arg pp0 =
      let pp1 : (compare zk arg = LT) = convLT _ _ pp0 in
      let pp2 : (compare yk arg = LT) = transitivity yk zk arg (reversion2 zk yk $ lemma1 zk yk ykp) pp1 in
      cong (\case { LT => True; _ => False }) pp2

    0 p3 : ((filter (xk >) $ filter (yk >) $ filter (zk >) keys) === (filter (xk >) $ filter (yk >) keys))
    p3 =
      let pp2 : ((filter (xk >) $ filter (zk >) $ filter (yk >) keys) === (filter (xk >) $ filter (yk >) $ filter (zk >) keys))
          = cong (filter (xk >)) filterCommutative
      in
      let pp3 : ((filter (xk >) $ filter (yk >) keys) === (filter (xk >) $ filter (zk >) $ filter (yk >) keys))
          = cong (filter (xk >)) $ sym $ filterImplication p2
      in
      sym $ trans pp3 pp2

    0 p4 : ((filter (xk <) $ filter (yk >) $ filter (zk >) keys) === (filter (xk <) $ filter (yk >) keys))
    p4 =
      let pp1 : ((filter (xk <) $ filter (zk >) $ filter (yk >) keys) === (filter (xk <) $ filter (yk >) $ filter (zk >) keys))
          = cong (filter (xk <)) filterCommutative
      in
      let pp2 : ((filter (xk <) $ filter (yk >) keys) === (filter (xk <) $ filter (zk >) $ filter (yk >) keys))
          = cong (filter (xk <)) $ sym $ filterImplication p2
      in
      sym $ trans pp2 pp1

    0 p5 : ((filter (yk <) $ filter (zk >) keys) === (filter (zk >) $ filter (yk <) keys))
    p5 = filterCommutative

    0 p6 : (filter (zk <) keys) === (filter (zk <) $ filter (yk <) keys)
    p6 =
      let pp0 : ((filter (yk <) $ filter (zk <) keys) === (filter (zk <) keys))
          = filterImplication p2'
      in
      let pp1 : ((filter (zk <) $ filter (yk <) keys) === (filter (yk <) $ filter (zk <) keys))
          = filterCommutative
      in
      sym $ trans pp1 pp0
  in
  let a' : GoodTree {keys = filter (xk >) $ filter (yk >) keys} = rewrite sym p3 in a in
  let b' : GoodTree {keys = filter (xk <) $ filter (yk >) keys} = rewrite sym p4 in b in
  let c' : GoodTree {keys = filter (zk >) $ filter (yk <) keys} = rewrite sym p5 in c in
  let d' : GoodTree {keys = filter (zk <) $ filter (yk <) keys} = rewrite sym p6 in d in
  let l' = BlackNode xk xv a' b' {kp = p1} in
  let r' = BlackNode zk zv c' d' {kp = inFilter (yk <) (zk ==) p0 _ zkp} in
  Evidence Red $ RedNode yk yv l' r' {kp = outFilter ykp}
balanceLeft zk zv (BadRedNode {kp = ykp} yk yv a@(BlackNode _ _ _ _) b@(BlackNode _ _ _ _)) c =
  Evidence Black $ BlackNode {kp = zkp} zk zv (RedNode {kp = ykp} yk yv a b) c
balanceLeft zk zv (BadRedNode {kp = ykp} yk yv a@(BlackNode _ _ _ _) b@(Empty _)) c impossible
balanceLeft zk zv (BadRedNode {kp = ykp} yk yv a@(Empty _) b@(BlackNode _ _ _ _)) c impossible
balanceLeft zk zv (BadRedNode {kp = ykp} yk yv a@(Empty _) b@(Empty _)) c =
  Evidence Black $ BlackNode {kp = zkp} zk zv (RedNode {kp = ykp} yk yv a b) c

balanceRight :
  (kord : LawfulOrd kt) =>
  (zk : kt) ->
  {0 zkp : In (zk ==) keys} ->
  vt zk ->
  GoodTree {height, color = colorLeft, kt, kord, keys = filter (zk >) keys, vt} ->
  BadTree {height, kt, kord, keys = filter (zk <) keys, vt} ->
  Exists \color : Color => GoodTree {height = S height, color, kt, kord, keys, vt}

mutual
  insertLeft :
    (kord : LawfulOrd kt) =>
    {0 colorLeft : Color} ->
    (k : kt) ->
    vt k ->
    (k' : kt) ->
    {0 kp : In (k' ==) keys} ->
    vt k' ->
    {0 ltEq : compare k k' = LT} ->
    {0 keyslEq : keysl = filter (k' >) keys} ->
    GoodTree {height, color = colorLeft, kt, kord, keys = keysl, vt} ->
    {0 keysrEq : keysr = filter (k' <) keys} ->
    GoodTree {height, color = colorRight, kt, kord, keys = keysr, vt} ->
    (
      GoodBadTree colorLeft {height, kt, kord, vt, keys = filter (k' >) (k :: keys)},
      GoodTree {color = colorRight, height, kt, kord, vt, keys = filter (k' <) (k :: keys)}
    )
  insertLeft k v k' v' l r =
    let l' = insertG k v l in
    let 0 p1 = reversion1 k k' ltEq in
    let 0 p2 = cong (\case { GT => True; _ => False }) p1 in
    let 0 p3 : (k :: filter (k' >) keys = filter (k' >) (k :: keys)) = rewrite p2 in Refl in
    let l'' : GoodBadTree colorLeft {height, kt, kord, vt, keys = filter (k' >) (k :: keys)} =
      rewrite sym p3 in rewrite sym keyslEq in l'
    in
    let 0 p4 : (k' < k = False) = cong (\case { LT => True; _ => False }) p1 in
    let 0 p5 : (filter (k' <) keys = filter (k' <) (k :: keys)) = rewrite p4 in Refl in
    let r' : GoodTree {color = colorRight, height, kt, kord, vt, keys = filter (k' <) (k :: keys)} =
      rewrite sym p5 in rewrite sym keysrEq in r
    in
    (l'', r')

  insertRight :
    (kord : LawfulOrd kt) =>
    {0 colorLeft : Color} ->
    (k : kt) ->
    vt k ->
    (k' : kt) ->
    {0 kp : In (k' ==) keys} ->
    vt k' ->
    {0 gtEq : compare k k' = GT} ->
    {0 keyslEq : keysl = filter (k' >) keys} ->
    GoodTree {height, color = colorLeft, kt, kord, keys = keysl, vt} ->
    {0 keysrEq : keysr = filter (k' <) keys} ->
    GoodTree {height, color = colorRight, kt, kord, keys = keysr, vt} ->
    (
      GoodTree {color = colorLeft, height, kt, kord, vt, keys = filter (k' >) (k :: keys)},
      GoodBadTree colorRight {height, kt, kord, vt, keys = filter (k' <) (k :: keys)}
    )
  insertRight k v k' v' l r =
    let r' = insertG k v r in
    let 0 p1 = reversion2 k k' gtEq in
    let 0 p2 = cong (\case { LT => True; _ => False }) p1 in
    let 0 p3 : (k :: filter (k' <) keys = filter (k' <) (k :: keys)) = rewrite p2 in Refl in
    let r'' : GoodBadTree colorRight {height, kt, kord, vt, keys = filter (k' <) (k :: keys)} =
      rewrite sym p3 in rewrite sym keysrEq in r'
    in
    let 0 p4 : (k' > k = False) = cong (\case { GT => True; _ => False }) p1 in
    let 0 p5 : (filter (k' >) keys = filter (k' >) (k :: keys)) = rewrite p4 in Refl in
    let l' : GoodTree {color = colorLeft, height, kt, kord, vt, keys = filter (k' >) (k :: keys)} =
      rewrite sym p5 in rewrite sym keyslEq in l
    in
    (l', r'')

  insertG :
    {0 color : Color} ->
    (kord : LawfulOrd kt) =>
    (k : kt) ->
    vt k ->
    GoodTree {kt, height, color, kord, vt, keys} ->
    GoodBadTree color {height, kt, kord, vt, keys = k :: keys}
  insertG k v (Empty Refl) =
    let 0 kp : (In (k ==) (k :: [])) = MkIn k (cong (\case {EQ => True; _ => False}) $ reflexivity k) [] in
    Evidence Red (
      RedNode k v
        (rewrite reflexivity k in Empty Refl)
        (rewrite reflexivity k in Empty Refl)
        {keys = k :: [], kp}
    )
  insertG k v (RedNode k' v' l r {kp}) =
    case the (Subset Ordering (compare k k' ===)) $ Element (compare k k') Refl of
      Element LT ltEq =>
        let (Evidence color' l', r') = insertLeft k v k' v' l r {ltEq, kp, keyslEq = Refl, keysrEq = Refl} in
        BadRedNode k' v' l' r' {kp = MkInCons k keys kp}
      Element EQ p0 =>
        let 0 p2 = funext (compare k') (compare k) (\x => equality1 k' k x (reversion3 k k' p0)) in
        let 0 helper2 : ((f : Ordering -> Bool) -> {auto p1 : f EQ = False} -> (filter (\x => f (compare k' x)) keys = filter (\x => f (compare k x)) (k :: keys)))
            helper2 f {p1} =
              rewrite reflexivity k in
              rewrite p1 in
              cong (\arg => filter (\x => f (arg x)) keys) p2
        in
        let l' : GoodTree {color = Black, height, kt, kord, vt, keys = filter (k >) (k :: keys)} =
            replace {p = \arg => GoodTree {color = Black, height, kt, kord, vt, keys = arg}}
              (helper2 (\case { GT => True; _ => False }))
              l
        in
        let r' : GoodTree {color = Black, height, kt, kord, vt, keys = filter (k <) (k :: keys)} =
            replace {p = \arg => GoodTree {color = Black, height, kt, kord, vt, keys = arg}}
              (helper2 (\case { LT => True; _ => False }))
              r
        in
        BadRedNode k v l' r' {kp = MkIn k (cong (\case { EQ => True; _ => False }) (reflexivity k)) keys}
      Element GT gtEq =>
        let (l', Evidence color' r') = insertRight k v k' v' l r {gtEq, kp, keyslEq = Refl, keysrEq = Refl} in
        BadRedNode k' v' l' r' {kp = MkInCons k keys kp}
  insertG k v (BlackNode k' v' l r {kp, height = height', colorLeft, colorRight}) = case the (Subset Ordering (compare k k' ===)) $ Element (compare k k') Refl of
    Element LT ltEq =>
      case l of
        Empty _ =>
          let (Evidence color' l', r') = insertLeft k v k' v' l r {ltEq, kp, keyslEq = Refl, keysrEq = Refl} in
          Evidence Black $ BlackNode k' v' l' r' {kp = MkInCons k keys kp}
        BlackNode _ _ _ _ =>
          let (Evidence color' l', r') = insertLeft k v k' v' l r {ltEq, kp, keyslEq = Refl, keysrEq = Refl} in
          Evidence Black $ BlackNode k' v' l' r' {kp = MkInCons k keys kp}
        RedNode _ _ _ _ =>
          let (l', r') = insertLeft k v k' v' l r {kp, ltEq, keyslEq = Refl, keysrEq = Refl} in
          balanceLeft k' v' l' r' {kord, zkp = MkInCons _ _ kp}
    Element EQ p0 =>
        let
          0 p5 : (x : kt) -> (k > x = k' > x)
          p5 x = cong (\case { GT => True; _ => False }) $ equality1 k k' x p0

          0 p6 : (x : kt) -> (k < x = k' < x)
          p6 x = cong (\case { LT => True; _ => False }) $ equality1 k k' x p0
        in
        let 0 p1 : (filter (k >) keys = (filter (k' >) keys)) = filterExtensionality p5 in
        let 0 p2 : (filter (k >) (k :: keys) = filter (k >) keys)
            = rewrite reflexivity k in Refl in
        let 0 p3 : (filter (k <) keys = (filter (k' <) keys)) = filterExtensionality p6 in
        let 0 p4 : (filter (k <) (k :: keys) = filter (k <) keys)
            = rewrite reflexivity k in Refl in
        let l' : GoodTree {color = colorLeft, height = height', kt, kord, vt, keys = filter (k >) (k :: keys)} =
            rewrite trans p2 p1 in l
        in
        let r' : GoodTree {color = colorRight, height = height', kt, kord, vt, keys = filter (k <) (k :: keys)} =
            rewrite trans p4 p3 in r
        in
        Evidence Black $ BlackNode k v l' r' {kp = MkIn k (cong (\case { EQ => True; _ => False }) (reflexivity k)) keys}
    Element GT gtEq =>
      case r of
        Empty _ =>
          let (l', Evidence color' r') = insertRight k v k' v' l r {gtEq, kp, keyslEq = Refl, keysrEq = Refl} in
          Evidence Black $ BlackNode k' v' l' r' {kp = MkInCons k keys kp}
        BlackNode _ _ _ _ =>
          let (l', Evidence color' r') = insertRight k v k' v' l r {gtEq, kp, keyslEq = Refl, keysrEq = Refl} in
          Evidence Black $ BlackNode k' v' l' r' {kp = MkInCons k keys kp}
        RedNode _ _ _ _ =>
          let (l', r') = insertRight k v k' v' l r {kp, gtEq, keyslEq = Refl, keysrEq = Refl} in
          balanceRight k' v' l' r' {kord, zkp = MkInCons _ _ kp}
