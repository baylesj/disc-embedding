/-
Copyright (c) 2026. Released under Apache 2.0 license.

# The generalized Schoenflies theorem (Book, Chapter 3)

Brown's theorem: a bicollared `(n-1)`-sphere in `Sⁿ` bounds an `n`-ball on each side.
Brown's proof is the book's first example of a shrinking argument: the key step is that
the quotient of `Sⁿ` by a cellular set is again `Sⁿ`.

Status: `cellular_quotient_approximable` is proved. `generalized_schoenflies` is proved
from the Jordan–Brouwer separation IOU and Brown's Theorem 5 (`Brown.lean`), whose
proof is still open.
-/
module

public import DiscEmbedding.Brown

@[expose] public section

namespace DiscEmbedding

open Metric Set Topology

/-- Shrinking a single cellular set in a sphere: if `A ⊆ Sⁿ` is cellular and
`q : Sⁿ → Sⁿ` is a continuous surjection collapsing exactly `A` to a point, then `q` is
approximable by homeomorphisms. This is the key step in Brown's proof.
(Book, Chapter 3.) See `IsCellular.approximableByHomeomorphisms_of_collapse` for the
general version. -/
theorem cellular_quotient_approximable (n : ℕ) (A : Set (Sphere (n + 1)))
    (hA : IsCellular n A)
    (q : Sphere (n + 1) → Sphere (n + 1)) (hq : Continuous q)
    (hsurj : Function.Surjective q)
    (hcollapse : ∃ p, q ⁻¹' {p} = A ∧ ∀ y ≠ p, (q ⁻¹' {y}).Subsingleton) :
    ApproximableByHomeomorphisms q := by
  obtain ⟨p, hpA, hp⟩ := hcollapse
  exact hA.approximableByHomeomorphisms_of_collapse hq hsurj hpA hp

/-- **Generalized Schoenflies theorem** (Brown 1960; Mazur; Morse).
Let `e : Sⁿ⁻¹ × [-1, 1] → Sⁿ` be an embedding (a bicollar). Then the complement of the
central sphere `e(Sⁿ⁻¹ × {0})` has exactly two components, and the closure of each is a
topological `n`-ball. -/
theorem generalized_schoenflies (n : ℕ)
    (e : Sphere n × Icc (-1 : ℝ) 1 → Sphere (n + 1)) (he : IsEmbedding e) :
    ∃ U V : Set (Sphere (n + 1)),
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V = (range fun x : Sphere n => e (x, collarZero))ᶜ ∧
      IsTopBall n (closure U) ∧ IsTopBall n (closure V) := by
  have hg : IsEmbedding fun x : Sphere n => e (x, collarZero) :=
    he.comp (isEmbedding_prodMkLeft collarZero)
  obtain ⟨U, V, hUo, hVo, hUc, hVc, hUV, hcov, -, -⟩ := jordan_brouwer_separation n _ hg
  refine ⟨U, V, hUo, hVo, hUc, hVc, hUV, hcov, ?_, ?_⟩
  · exact brown_closure_isTopBall n e he U V hUo hVo hUc hVc hUV hcov
  · exact brown_closure_isTopBall n e he V U hVo hUo hVc hUc hUV.symm
      (by rw [union_comm]; exact hcov)

end DiscEmbedding

end
