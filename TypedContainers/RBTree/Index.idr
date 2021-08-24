module TypedContainers.RBTree.Index

import Data.Nat
import Data.DPair
import Data.List
import TypedContainers.In
import TypedContainers.LawfulOrd
import TypedContainers.RBTree.Base

%default total

public export
data Erased : Type -> Type where
  MkErased : (0 _ : a) -> Erased a

helper : LawfulOrd a => (x : a) -> (y : a) -> (z : a) -> (x > y = True) -> (y == z = True) -> (x > z = True)
helper x y z p1 p2 =
  let p1' = convGT x y p1 in
  let p2' = convEQ y z p2 in
  let p3 = equality2 y z x p2' in
  let p4 : (compare x z = GT) = replace {p = \arg => arg = GT} p3 p1' in
  cong (\case {GT => True; _ => False}) p4

public export
indexG : {0 keys : List kt} -> {kord : LawfulOrd kt} -> (k : kt) -> {0 k_in_keys : In (k ==) keys} -> GoodTree {kt, kord, keys, vt} -> Exists $ \k' => Exists $ \_ : compare k' k = EQ => vt k'
indexG k (Empty Refl) impossible
indexG k (RedNode k' v l r) = case the (Subset Ordering (compare k' k ===)) $ Element (compare k' k) Refl of
  Element EQ p0 => Evidence k' $ Evidence p0 v
  Element GT p0 =>
    let 0 p1 = \x, p => helper k' k x (cong (\case {GT => True; _ => False}) p0) p in
    let 0 p2 : In (k ==) (filter (k' >) keys) = inFilter (k' >) (k ==) p1 keys k_in_keys in
    indexG k l {k_in_keys = p2}
  Element LT p0 =>
    let 0 p1 = \x, p => ( let p1' = replace {p = \arg => arg = LT} (equality2 k x k' (convEQ k x p)) p0 in let p1'' = cong (\case {LT => True; _ => False}) p1' in the (k' < x = True) p1'' ) in
    let 0 p2 : In (k ==) (filter (k' <) keys) = inFilter (k' <) (k ==) p1 keys k_in_keys in
    indexG k r {k_in_keys = p2}
indexG k (BlackNode k' v l r) = case the (Subset Ordering (compare k' k ===)) $ Element (compare k' k) Refl of
  Element EQ p0 => Evidence k' $ Evidence p0 v
  Element GT p0 =>
    let 0 p1 = \x, p => helper k' k x (cong (\case {GT => True; _ => False}) p0) p in
    let 0 p2 : In (k ==) (filter (k' >) keys) = inFilter (k' >) (k ==) p1 keys k_in_keys in
    indexG k l {k_in_keys = p2}
  Element LT p0 =>
    let 0 p1 = \x, p => ( let p1' = replace {p = \arg => arg = LT} (equality2 k x k' (convEQ k x p)) p0 in let p1'' = cong (\case {LT => True; _ => False}) p1' in the (k' < x = True) p1'' ) in
    let 0 p2 : In (k ==) (filter (k' <) keys) = inFilter (k' <) (k ==) p1 keys k_in_keys in
    indexG k r {k_in_keys = p2}

public export
indexGMaybe : {0 b : kt -> Type} -> {0 keys : List kt} -> {kord : LawfulOrd kt} -> (k : kt)
  -> {0 foldLeft : (Not $ In (k ==) keys) -> a}
  -> {0 foldRight : (k' : kt) -> (compare k' k = EQ, In (k' ==) keys) -> b k'}
  -> GoodTree {kt, kord, keys, vt}
  -> Either (Erased $ a) (DPair kt $ \k' => Exists $ \_ : b k' => vt k')
indexGMaybe k (Empty Refl) = Left $ MkErased $ foldLeft $ \p => case p of
  MkIn _ _ _ impossible
  MkInCons _ _ _ impossible
indexGMaybe k (RedNode k' v l r {kp}) = case the (Subset Ordering (compare k' k ===)) $ Element (compare k' k) Refl of
  Element EQ p0 => Right $ MkDPair k' $ Evidence (foldRight k' (p0, kp)) v
  Element GT p0 =>
    let
      0 p1 : (x : kt) -> (k == x = True) -> (k' > x = True)
      p1 x pp0 = cong (\case { GT => True; _ => False }) $ sym $ trans (sym p0) (equality2 k x k' (convEQ k x pp0))

      0 foldLeft' : (In (k ==) (filter (k' >) keys) -> Void) -> a
      foldLeft' pp0 = foldLeft $ \pp1 => pp0 $ inFilter (k' >) (k ==) p1 keys pp1

      0 foldRight' : (k'' : kt) -> (compare k'' k = EQ, In (k'' ==) (filter (k' >) keys)) -> b k''
      foldRight' k'' (pp0, pp1) = foldRight k'' (pp0, outFilter pp1)
    in
    indexGMaybe k {foldLeft = foldLeft', foldRight = foldRight'} l
  Element LT p0 =>
    let
      0 p1 : (x : kt) -> (k == x = True) -> (k' < x = True)
      p1 x pp0 = cong (\case { LT => True; _ => False }) $ sym $ trans (sym p0) (equality2 k x k' (convEQ k x pp0))

      0 foldLeft' : (In (k ==) (filter (k' <) keys) -> Void) -> a
      foldLeft' pp0 = foldLeft $ \pp1 => pp0 $ inFilter (k' <) (k ==) p1 keys pp1

      0 foldRight' : (k'' : kt) -> (compare k'' k = EQ, In (k'' ==) (filter (k' <) keys)) -> b k''
      foldRight' k'' (pp0, pp1) = foldRight k'' (pp0, outFilter pp1)
    in
    indexGMaybe k {foldLeft = foldLeft', foldRight = foldRight'} r
indexGMaybe k (BlackNode k' v l r {kp}) = case the (Subset Ordering (compare k' k ===)) $ Element (compare k' k) Refl of
  Element EQ p0 => Right $ MkDPair k' $ Evidence (foldRight k' (p0, kp)) v
  Element GT p0 =>
    let
      0 p1 : (x : kt) -> (k == x = True) -> (k' > x = True)
      p1 x pp0 = cong (\case { GT => True; _ => False }) $ sym $ trans (sym p0) (equality2 k x k' (convEQ k x pp0))

      0 foldLeft' : (In (k ==) (filter (k' >) keys) -> Void) -> a
      foldLeft' pp0 = foldLeft $ \pp1 => pp0 $ inFilter (k' >) (k ==) p1 keys pp1

      0 foldRight' : (k'' : kt) -> (compare k'' k = EQ, In (k'' ==) (filter (k' >) keys)) -> b k''
      foldRight' k'' (pp0, pp1) = foldRight k'' (pp0, outFilter pp1)
    in
    indexGMaybe k {foldLeft = foldLeft', foldRight = foldRight'} l
  Element LT p0 =>
    let
      0 p1 : (x : kt) -> (k == x = True) -> (k' < x = True)
      p1 x pp0 = cong (\case { LT => True; _ => False }) $ sym $ trans (sym p0) (equality2 k x k' (convEQ k x pp0))

      0 foldLeft' : (In (k ==) (filter (k' <) keys) -> Void) -> a
      foldLeft' pp0 = foldLeft $ \pp1 => pp0 $ inFilter (k' <) (k ==) p1 keys pp1

      0 foldRight' : (k'' : kt) -> (compare k'' k = EQ, In (k'' ==) (filter (k' <) keys)) -> b k''
      foldRight' k'' (pp0, pp1) = foldRight k'' (pp0, outFilter pp1)
    in
    indexGMaybe k {foldLeft = foldLeft', foldRight = foldRight'} r
