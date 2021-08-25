import TypedContainers.LawfulOrd

%default total

LawfulOrd Nat where
  compare Z Z = EQ
  compare Z (S _) = LT
  compare (S _) Z = GT
  compare (S x) (S y) = TypedContainers.LawfulOrd.compare x y
  
  reflexivity Z = Refl
  reflexivity (S x) = reflexivity x

  reversion1 Z Z p impossible
  reversion1 (S _) Z p impossible
  reversion1 Z (S _) p = Refl
  reversion1 (S x) (S y) p =
    let rec = reversion1 x y in
    rec p

  reversion2 Z Z p impossible
  reversion2 (S _) Z p = Refl
  reversion2 Z (S _) p impossible
  reversion2 (S x) (S y) p =
    let rec = reversion2 x y in
    rec p

  reversion3 Z Z p = Refl
  reversion3 (S _) Z p impossible
  reversion3 Z (S _) p impossible
  reversion3 (S x) (S y) p =
    let rec = reversion3 x y in
    rec p

  transitivity Z     Z     Z     p0 p1 impossible
  transitivity Z     Z     (S z) p0 p1 impossible
  transitivity Z     (S y) Z     p0 p1 impossible
  transitivity Z     (S y) (S z) p0 p1 = Refl
  transitivity (S x) Z     Z     p0 p1 impossible
  transitivity (S x) Z     (S z) p0 p1 impossible
  transitivity (S x) (S y) Z     p0 p1 impossible
  transitivity (S x) (S y) (S z) p0 p1 =
    let rec = transitivity x y z p0 p1 in
    rec

  equality1 Z     Z     z     p = Refl
  equality1 Z     (S y) Z     p impossible
  equality1 Z     (S y) (S z) p impossible
  equality1 (S x) Z     Z     p impossible
  equality1 (S x) Z     (S z) p impossible
  equality1 (S x) (S y) Z     p = Refl
  equality1 (S x) (S y) (S z) p =
    let rec = equality1 x y z p in
    rec

  equality2 Z     Z     z     p = Refl
  equality2 Z     (S y) Z     p impossible
  equality2 Z     (S y) (S z) p impossible
  equality2 (S x) Z     Z     p impossible
  equality2 (S x) Z     (S z) p impossible
  equality2 (S x) (S y) Z     p = Refl
  equality2 (S x) (S y) (S z) p =
    let rec = equality2 x y z p in
    rec

LawfullerOrd Nat where
  realEquality Z Z p = Refl
  realEquality Z (S _) p impossible
  realEquality (S _) Z p impossible
  realEquality (S x) (S y) p =
    let rec = realEquality x y p in
    cong S rec
