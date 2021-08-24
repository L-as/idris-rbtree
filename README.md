Type-safe verified Red-Black trees in Idris.

Check `TypedContainers/RBTree.idr` for the basic API.

NB: Spacetime complexity *should* be the same as standard Red-Black trees,
however, it has not been proven.

Features:
- Value type can depend on key

The algorithm is taken from *Purely functional data structures* by Chris Okasaki.
The proofs were mostly left as an exercise to the reader.
