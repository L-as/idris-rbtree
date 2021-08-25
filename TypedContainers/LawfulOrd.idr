module TypedContainers.LawfulOrd

%default total

public export
interface LawfulOrd a where
  compare : a -> a -> Ordering
  0 reflexivity : (x : a) -> (compare x x = EQ)
  0 reversion1 : (x : a) -> (y : a) -> (compare x y = LT) -> (compare y x = GT)
  0 reversion2 : (x : a) -> (y : a) -> (compare x y = GT) -> (compare y x = LT)
  0 reversion3 : (x : a) -> (y : a) -> (compare x y = EQ) -> (compare y x = EQ)
  0 transitivity : (x : a) -> (y : a) -> (z : a) -> (compare x y = LT) -> (compare y z = LT) -> (compare x z = LT)
  0 equality1 : (x : a) -> (y : a) -> (z : a) -> (compare x y = EQ) -> (compare x z = compare y z)
  0 equality2 : (x : a) -> (y : a) -> (z : a) -> (compare x y = EQ) -> (compare z x = compare z y)

public export
interface LawfulOrd a => LawfullerOrd a where
  -- `compare` needs to be unambigious here because the name is
  -- seemingly resolved where the instances are defined...
  0 realEquality : (x : a) -> (y : a) -> (TypedContainers.LawfulOrd.compare x y = EQ) -> (x = y)

public export
(==) : LawfulOrd a => a -> a -> Bool
x == y = case compare x y of { EQ => True; _ => False }

public export
(<) : LawfulOrd a => a -> a -> Bool
x < y = case compare x y of { LT => True; _ => False }

public export
(>) : LawfulOrd a => a -> a -> Bool
x > y = case compare x y of { GT => True; _ => False }

public export
convLT : LawfulOrd a => (x : a) -> (y : a) -> (x < y = True) -> (compare x y = LT)
convLT x y p with (compare x y)
  convLT x y Refl | GT impossible
  convLT x y Refl | EQ impossible
  convLT x y Refl | LT = Refl

public export
convGT : LawfulOrd a => (x : a) -> (y : a) -> (x > y = True) -> (compare x y = GT)
convGT x y p with (compare x y)
  convGT x y Refl | GT = Refl
  convGT x y Refl | EQ impossible
  convGT x y Refl | LT impossible

public export
convEQ : LawfulOrd a => (x : a) -> (y : a) -> (x == y = True) -> (compare x y = EQ)
convEQ x y p with (compare x y)
  convEQ x y Refl | GT impossible
  convEQ x y Refl | EQ = Refl
  convEQ x y Refl | LT impossible
