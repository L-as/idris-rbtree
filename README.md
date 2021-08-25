Type-safe verified red-black trees in Idris.

Check `TypedContainers/RBTree.idr` for the basic API.
Your key type needs to implement `LawfulOrd` (see `TypedContainers/LawfulOrd.idr`).

NB: Space complexities and time complexities *should* be the same as standard Red-Black trees,
however, it has not been proven.

Features:
- Value type can depend on key

The algorithm is taken from *Purely functional data structures* by Chris Okasaki.
The proofs were mostly left as an exercise to the reader.
The only difference is that the root of the tree isn't always made red,
since this isn't always required.
