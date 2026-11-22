/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Basic models: discs, spheres, topological balls

We model the closed `n`-disc as the closed unit ball of `Fin n → ℝ` with Mathlib's
default (sup) metric, i.e. the cube `[-1, 1]ⁿ`, and the `(n-1)`-sphere as its boundary.
These are homeomorphic to the round disc and sphere, and everything in Part I of
*The Disc Embedding Theorem* is invariant under homeomorphism, so this choice is
harmless. It also keeps the import footprint small (no inner-product spaces).
If we later want to match `EuclideanSpace ℝ (Fin n)`, we only change these
definitions and prove the comparison homeomorphism once.
-/
module

public import DiscEmbedding.Imports

@[expose] public section

namespace DiscEmbedding

open Metric Set Topology

/-- The model closed `n`-disc `Dⁿ`: the closed unit ball of `Fin n → ℝ` (sup metric). -/
abbrev Disc (n : ℕ) : Set (Fin n → ℝ) := closedBall 0 1

/-- The model `(n-1)`-sphere `Sⁿ⁻¹ = ∂Dⁿ`: the unit sphere of `Fin n → ℝ` (sup metric).

Note the indexing: `Sphere n` is the boundary of `Disc n`, so it is `(n-1)`-dimensional,
and `Sphere (n + 1)` is the `n`-sphere. -/
abbrev Sphere (n : ℕ) : Set (Fin n → ℝ) := sphere 0 1

/-- A subset `B` of a space `X` is a *topological `n`-ball* if, with the subspace topology,
it is homeomorphic to the model disc `Dⁿ`. -/
def IsTopBall (n : ℕ) {X : Type*} [TopologicalSpace X] (B : Set X) : Prop :=
  Nonempty (B ≃ₜ Disc n)

/-- A subset `A` of a space `M` is *cellular* (of dimension `n`) if it is the intersection
of a nested sequence of closed `n`-balls `Bᵢ = eᵢ(Dⁿ)`, each contained in the interior of
the previous one. (Book, Chapter 3.)

We take each ball to be *collared*: it is the image of the closed unit ball under an
open embedding `eᵢ : ℝⁿ → M`, and "interior" means `eᵢ` of the open unit ball. When `M`
is an `n`-manifold this is equivalent to the book's definition (using arbitrary
topological balls with `Bᵢ₊₁ ⊆ int Bᵢ`), but proving the equivalence needs invariance
of domain, which Mathlib does not yet have. The collared version is what Brown's proof
of the generalized Schoenflies theorem produces, so nothing is lost for our purposes. -/
def IsCellular (n : ℕ) {M : Type*} [TopologicalSpace M] (A : Set M) : Prop :=
  ∃ e : ℕ → (Fin n → ℝ) → M, (∀ i, IsOpenEmbedding (e i)) ∧
    (∀ i, e (i + 1) '' closedBall 0 1 ⊆ e i '' ball 0 1) ∧
    A = ⋂ i, e i '' closedBall 0 1

/-- The point `0 ∈ [-1, 1]`, used to pick out the central slice of a bicollar. -/
def collarZero : Icc (-1 : ℝ) 1 := ⟨0, by norm_num, by norm_num⟩

end DiscEmbedding

end
