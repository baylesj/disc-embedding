/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Brown's proof of the generalized Schoenflies theorem

We follow M. Brown, *A proof of the generalized Schoenflies theorem*,
Bull. AMS 66 (1960), 74–76, as presented in Chapter 3 of the book. Brown's Theorems 4
and 5 are stated here (Theorem 1 is in `BrownCollapse.lean`); Theorems 0, 2 and 3 are intermediate steps that appear only in
the blueprint for now.

* Theorem 0 (blueprint only): if `f : Q → Sⁿ` is a map of an `n`-cell with finitely many
  inverse sets, then `f(Q)` is `f(∂Q)` together with one complementary domain of
  `f(∂Q)`. Uses all three IOUs.
* Theorem 1 (`brown_collapse_cellular`, proved in `BrownCollapse.lean`): a cellular set
  inside a cell can be collapsed by a self-map of the cell fixed on the boundary. Needs
  no IOUs.
* Theorem 2 (blueprint only): if a complementary domain `D` maps onto a cell with a
  single cellular inverse set, then `D` is a cell.
* Theorem 3 (blueprint only): the only inverse set of a map `Q → Sⁿ` is cellular.
* Theorem 4 (`brown_two_inverse_sets`): if `f : Sⁿ → Sⁿ` has exactly two inverse sets,
  both are cellular.
* Theorem 5 (`brown_closure_isTopBall`): the closure of each side of a bicollared sphere
  is a ball.

An *inverse set* of `f` is a fiber `f ⁻¹' {y}` with at least two points.

Status: Theorem 1 is proved. Theorems 4 and 5 are stated only.
-/
module

public import DiscEmbedding.IOU
public import DiscEmbedding.BrownCollapse

@[expose] public section

namespace DiscEmbedding

open Metric Set Function Topology

/-- **Brown's Theorem 4.** If a continuous surjection `f : Sⁿ → Sⁿ` has exactly two
inverse sets `A` and `B`, then both are cellular. -/
theorem brown_two_inverse_sets (n : ℕ) (f : Sphere (n + 1) → Sphere (n + 1))
    (hf : Continuous f) (hsurj : Surjective f) {a b : Sphere (n + 1)} (hab : a ≠ b)
    (hA : (f ⁻¹' {a}).Nontrivial) (hB : (f ⁻¹' {b}).Nontrivial)
    (hrest : ∀ y, y ≠ a → y ≠ b → (f ⁻¹' {y}).Subsingleton) :
    IsCellular n (f ⁻¹' {a}) ∧ IsCellular n (f ⁻¹' {b}) := by
  sorry

/-- **Brown's Theorem 5.** Let `e : Sⁿ⁻¹ × [-1, 1] → Sⁿ` be a bicollar of
`Σ = e(Sⁿ⁻¹ × {0})`, and let `U, V` be the two components of `Sⁿ ∖ Σ`. Then the closure
of `U` is an `n`-ball. (Applying this with `U` and `V` swapped handles the other side.)

Proof idea: collapse the parts of `U` and `V` beyond the collar to the two poles of
`Sⁿ` and map the collar onto `Sⁿ` minus the poles by the suspension coordinates. By
Theorem 4 both collapsed sets are cellular; Theorems 1 and 2 then show the closure
of each side is a cell. -/
theorem brown_closure_isTopBall (n : ℕ) (e : Sphere n × Icc (-1 : ℝ) 1 → Sphere (n + 1))
    (he : IsEmbedding e) (U V : Set (Sphere (n + 1))) (hU : IsOpen U) (hV : IsOpen V)
    (hUc : IsConnected U) (hVc : IsConnected V) (hUV : Disjoint U V)
    (hcov : U ∪ V = (range fun x : Sphere n => e (x, collarZero))ᶜ) :
    IsTopBall n (closure U) := by
  sorry

end DiscEmbedding

end
