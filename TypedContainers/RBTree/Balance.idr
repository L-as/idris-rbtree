module TypedContainers.RBTree.Balance

import Data.DPair
import Data.List
import TypedContainers.In
import TypedContainers.LawfulOrd
import TypedContainers.RBTree.Base
import TypedContainers.Util.Filter

%default total

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

public export
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

public export
balanceRight :
  (kord : LawfulOrd kt) =>
  (xk : kt) ->
  {0 xkp : In (xk ==) keys} ->
  vt xk ->
  GoodTree {height, color = colorLeft, kt, kord, keys = filter (xk >) keys, vt} ->
  BadTree {height, kt, kord, keys = filter (xk <) keys, vt} ->
  Exists \color : Color => GoodTree {height = S height, color, kt, kord, keys, vt}
balanceRight xk xv a (BadRedNode {kp = zkp} zk zv (RedNode yk yv b c {kp = ykp}) d) =
  let
    0 p0 : (arg : kt) -> (yk < arg = True) -> (xk < arg = True)
    p0 arg pp0 =
      let pp1 : (compare yk arg = LT) = convLT _ _ pp0 in
      let pp2 : (compare xk arg = LT) = transitivity xk yk arg (lemma0 xk yk (outFilter ykp)) pp1 in
      cong (\case { LT => True; _ => False }) pp2

    0 p0' : (arg : kt) -> (zk < arg = True) -> (yk < arg = True)
    p0' arg pp0 =
      let pp1 : (compare zk arg = LT) = convLT _ _ pp0 in
      let pp2 : (compare yk arg = LT) = transitivity yk zk arg (reversion2 zk yk $ lemma1 zk yk ykp) pp1 in
      cong (\case { LT => True; _ => False }) pp2

    0 p1 : (arg : kt) -> (yk > arg = True) -> (zk > arg = True)
    p1 arg pp0 =
      let pp1 : (compare arg yk = LT) = reversion2 yk arg $ convGT _ _ pp0 in
      let pp2 : (compare yk zk = LT) = reversion2 zk yk $ lemma1 zk yk ykp in
      let pp3 : (compare arg zk = LT) = transitivity arg yk zk pp1 pp2 in
      cong (\case { GT => True; _ => False }) $ reversion1 arg zk pp3

    0 p2 : (arg : kt) -> (xk > arg = True) -> (yk > arg = True)
    p2 arg pp0 =
      let pp1 : (compare arg xk = LT) = reversion2 xk arg $ convGT _ _ pp0 in
      let pp2 : (compare xk yk = LT) = lemma0 xk yk (outFilter ykp) in
      let pp3 : (compare arg yk = LT) = transitivity arg xk yk pp1 pp2 in
      cong (\case { GT => True; _ => False }) $ reversion1 arg yk pp3

    0 p3 : (filter (xk >) $ filter (yk >) keys) === (filter (xk >) keys)
    p3 = trans filterCommutative $ filterImplication p2

    0 p4 : (filter (xk <) $ filter (yk >) keys) === (filter (yk >) $ filter (zk >) $ filter (xk <) keys)
    p4 = trans filterCommutative $ trans (sym $ filterImplication p1) filterCommutative

    0 p5 : (filter (zk >) $ filter (yk <) keys) === (filter (yk <) $ filter (zk >) $ filter (xk <) keys)
    p5 = trans (cong (filter (zk >))
      $ sym $ filterImplication p0)
      $ trans (cong (filter (zk >)) filterCommutative) filterCommutative

    0 p6 : (filter (zk <) $ filter (yk <) keys) === (filter (zk <) $ filter (xk <) keys)
    p6 =
      let
        pp0 : (filter (yk <) $ filter (zk <) $ filter (xk <) keys) === (filter (zk <) $ filter (xk <) keys)
        pp0 = filterImplication p0'
        pp1 : (filter (yk <) $ filter (xk <) $ filter (zk <) keys) === (filter (yk <) $ filter (zk <) $ filter (xk <) keys)
        pp1 = cong (filter (yk <)) filterCommutative
        pp2 : (filter (xk <) $ filter (yk <) $ filter (zk <) keys) === (filter (yk <) $ filter (xk <) $ filter (zk <) keys)
        pp2 = filterCommutative
        pp3 : (filter (yk <) $ filter (zk <) keys) === (filter (xk <) $ filter (yk <) $ filter (zk <) keys)
        pp3 = sym $ filterImplication p0
        pp4 : (filter (zk <) $ filter (yk <) keys) === (filter (yk <) $ filter (zk <) keys)
        pp4 = filterCommutative
      in
      trans pp4 $ trans pp3 $ trans pp2 $ trans pp1 pp0

    0 p7 : (arg : kt) -> (xk == arg = True) -> (yk > arg = True)
    p7 arg pp0 =
      let pp1 = lemma0 xk yk (outFilter ykp) in
      let pp2 = trans (sym pp1) $ equality1 xk arg yk (convEQ xk arg pp0) in
      cong (\case { GT => True; _ => False }) $ reversion1 arg yk $ sym pp2

    0 p8 : (arg : kt) -> (zk == arg = True) -> (yk < arg = True)
    p8 arg pp0 =
      let pp1 = lemma1 zk yk ykp in
      let pp2 = trans (sym pp1) $ equality1 zk arg yk (convEQ zk arg pp0) in
      cong (\case { LT => True; _ => False }) $ reversion2 arg yk $ sym pp2
  in
  let a' : GoodTree {keys = filter (xk >) $ filter (yk >) keys} = rewrite p3 in a in
  let b' : GoodTree {keys = filter (xk <) $ filter (yk >) keys} = rewrite p4 in b in
  let c' : GoodTree {keys = filter (zk >) $ filter (yk <) keys} = rewrite p5 in c in
  let d' : GoodTree {keys = filter (zk <) $ filter (yk <) keys} = rewrite p6 in d in
  let l' = BlackNode xk xv a' b' {kp = inFilter (yk >) (xk ==) p7 _ xkp} in
  let r' = BlackNode zk zv c' d' {kp = inFilter (yk <) (zk ==) p8 _ (outFilter zkp)} in
  Evidence Red $ RedNode yk yv l' r' {kp = outFilter $ outFilter ykp}
balanceRight xk xv a (BadRedNode {kp = ykp} yk yv b (RedNode zk zv c d {kp = zkp})) = ?h1
balanceRight _ _ _ (BadRedNode _ _ (Empty _) (BlackNode _ _ _ _)) impossible
balanceRight _ _ _ (BadRedNode _ _ (BlackNode _ _ _ _) (Empty _)) impossible
balanceRight xk xv a (BadRedNode {kp = ykp} yk yv b@(BlackNode _ _ _ _) c@(BlackNode _ _ _ _)) =
  Evidence Black $ BlackNode {kp = xkp} xk xv a (RedNode {kp = ykp} yk yv b c)
balanceRight xk xv a (BadRedNode {kp = ykp} yk yv b@(Empty _) c@(Empty _)) =
  Evidence Black $ BlackNode {kp = xkp} xk xv a (RedNode {kp = ykp} yk yv b c)
