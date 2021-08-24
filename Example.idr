import TypedContainers.RBTree
import TypedContainers.LawfulOrd.Nat
import TypedContainers.LawfulOrd

mytree : RBTree Nat (\_ => Nat)
mytree = empty

mytree' : RBTree Nat (\_ => Nat)
mytree' =
  insert 5 10 .
  insert 2 4 .
  insert 8 16 $
  mytree
