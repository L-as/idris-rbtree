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
  reversion1 (S x) (S y) p = ?h1

  reversion2 x y p = ?h2
  reversion3 x y p = ?h3

  transitivity x y z p = ?h4

  equality1 x y z p = ?h5
  equality2 x y z p = ?h6
