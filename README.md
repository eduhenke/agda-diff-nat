# DiffNat: Difference Naturals in Agda

This project implements "Difference Naturals" (DiffNat) in Agda, providing an alternative representation of natural numbers that the following properties hold **definitionally**, not just propositionally:

1. Left identity: `0 + n ≡ n`
2. Right identity: `n + 0 ≡ n`
3. Associativity: `(l + m) + n ≡ l + (m + n)`

This means these equalities hold by definition (up to beta-reduction), without the need for additional proofs or rewrites.

## Acknowledgments

This project is adapted from [agda-assoc-free](https://github.com/agda/agda-assoc-free/tree/master), which implements DiffNat, but using irrelevant projections and the `irrAx` axiom.
