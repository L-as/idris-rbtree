module TypedContainers.RBTree.Insert

import Data.Nat
import Data.DPair
import Data.List
import TypedContainers.In
import TypedContainers.LawfulOrd
import TypedContainers.RBTree.Base
import TypedContainers.RBTree.Balance
import TypedContainers.Util.Filter

%default total

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
        let l' : GoodTree {kt, kord, vt, keys = filter (k >) (k :: keys)} =
            rewrite trans p2 p1 in l
        in
        let r' : GoodTree {kt, kord, vt, keys = filter (k <) (k :: keys)} =
            rewrite trans p4 p3 in r
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
          balanceRight k' v' l' r' {kord, xkp = MkInCons _ _ kp}

public export
insertG' :
  {0 color : Color} ->
  (kord : LawfulOrd kt) =>
  (k : kt) ->
  vt k ->
  GoodTree {kt, height, color, kord, vt, keys} ->
  Exists \color' => Exists \height' => GoodTree {color = color', height = height', kt, kord, vt, keys = k :: keys}
insertG' k v tree@(Empty Refl) =
  let Evidence color' tree' = insertG k v tree in
  Evidence color' $ Evidence 0 tree'
insertG' k v tree@(BlackNode _ _ _ _ {height = height'}) =
  let Evidence color' tree' = insertG k v tree in
  Evidence color' $ Evidence (S height') tree'
insertG' k v tree@(RedNode _ _ _ _) =
  let BadRedNode k' v' l r {height = height', kp} = insertG k v tree in
  Evidence Black $ Evidence (S height') $ BlackNode k' v' l r {kp}
