module TypedContainers.RBTree.Insert

import Data.Nat
import Data.DPair
import Data.List
import TypedContainers.In
import TypedContainers.LawfulOrd
import TypedContainers.RBTree.Base

-- TODO: Find out a way to do this without extensional function equality
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

lemma0 : LawfulOrd kt => {keys : List kt} -> (xk : kt) -> (yk : kt) -> In (yk ==) (filter (xk <) keys) -> (compare xk yk = LT)
lemma0 xk yk p0 =
  let MkDPair v (p3, p4) = extractIn p0 in
  let p5 = equality2 _ _ xk (convEQ _ _ p3) in
  let p6 = convLT xk v p4 in
  trans p5 p6

balanceLeft :
  (kord : LawfulOrd kt) =>
  (zk : kt) ->
  {0 zkp : In (zk ==) keys} ->
  vt zk ->
  {0 keyslEq : keysl = filter (zk >) keys} ->
  BadTree {height, kt, kord, keys = keysl, vt} ->
  {0 keysrEq : keysr = filter (zk <) keys} ->
  GoodTree {height, color = colorRight, kt, kord, keys = keysr, vt} ->
  Exists \color : Color => GoodTree {height = S height, color, kt, kord, keys = keys, vt}
balanceLeft zk zv (BadRedNode {kp = xkp} xk xv a (RedNode yk yv b c {kp = ykp})) d =
  let
    0 ykp' : (In (yk ==) keysl) = outFilter ykp
    0 ykp' : (In (yk ==) (filter (zk >) keys)) = rewrite sym keyslEq in ykp'
    0 ykp' = outFilter ykp'

    0 yk_gt_xk : (GT = compare yk xk) = sym $ reversion1 xk yk $ lemma0 xk yk ykp

    0 xkp' : In (xk ==) keys = outFilter $ replace {p = \arg => In (xk ==) arg} keyslEq xkp

    0 p0 : (arg : kt) -> (xk == arg = True) -> (yk > arg = True)
    p0 arg prr =
      let pp0 = reversion1 xk yk $ lemma0 xk yk ykp in
      let pp1 = equality2 xk arg yk (convEQ xk arg prr) in
      let pp2 = trans (sym pp1) pp0 in
      cong (\case { GT => True; _ => False }) pp2

    newleft := BlackNode xk xv (?ha a) (?hb b) {kp = inFilter (yk >) (xk ==) p0 _ xkp'}
  in
  Evidence Red $ RedNode yk yv newleft ?r {kp = ykp'}
--balanceLeft zk zv (BadRedNode yk yv (RedNode xk xv a b) c) d = Evidence Red $ RedNode yk yv (BlackNode xk xv a b) (BlackNode zk zv c d)
--balanceLeft xk xv (BadRedNode yk yv (BlackNode zk zv a b) (BlackNode wk wv c d)) e = Evidence Black $ BlackNode xk xv (RedNode yk yv (BlackNode zk zv a b) (BlackNode wk wv c d)) e
--balanceLeft xk xv (BadRedNode yk yv Empty Empty) e = Evidence Black $ BlackNode xk xv (RedNode yk yv Empty Empty) e
balanceLeft _ _ _ _ = ?balanceLeftHole

balanceRight :
  (kord : LawfulOrd kt) =>
  (zk : kt) ->
  {0 zkp : In (zk ==) keys} ->
  vt zk ->
  {0 keyslEq : keysl = filter (zk >) keys} ->
  GoodTree {height, color = colorLeft, kt, kord, keys = keysl, vt} ->
  {0 keysrEq : keysr = filter (zk <) keys} ->
  BadTree {height, kt, kord, keys = keysr, vt} ->
  Exists \color : Color => GoodTree {height = S height, color, kt, kord, keys = keys, vt}
balanceRight = ?balanceRightHole

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
    let kp : (In (k ==) (k :: [])) = MkIn k (cong (\case {EQ => True; _ => False}) $ reflexivity k) [] in
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
  insertG k v whole@(BlackNode k' v' l r {kp, height = height'}) = case the (Subset Ordering (compare k k' ===)) $ Element (compare k k') Refl of
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
          balanceLeft k' v' l' r' {kord}
    Element EQ p0 => ?hgt
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
          balanceRight k' v' l' r' {kord}
  insertG _ _ _ = ?insertGHole
