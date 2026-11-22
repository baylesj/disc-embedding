/-
Copyright (c) 2026. Released under Apache 2.0 license.

# IOUs: classical algebraic topology not yet in Mathlib

Brown's proof of the generalized Schoenflies theorem relies on three classical results.
All of them follow from degree theory, or from computing the homology of spheres, and
none of them is in Mathlib yet. We state them here, in our cube model, as explicit
`sorry`s so that every other result can be proved relative to them.

Discharging these is a self-contained project, independent of Freedman's work and
valuable to Mathlib in its own right.

* `no_retraction`: there is no retraction of `Dⁿ` onto `∂Dⁿ` (Brouwer).
* `invariance_of_domain`: an injective continuous map from an open subset of `ℝⁿ` to
  `ℝⁿ` has open image (Brouwer).
* `jordan_brouwer_separation`: an embedded `(n-1)`-sphere in `Sⁿ` separates it into
  exactly two components, each with the sphere as its frontier.
-/
module

public import DiscEmbedding.Basic

@[expose] public section

namespace DiscEmbedding

open Metric Set Topology

/-- **IOU (Brouwer's no-retraction theorem).** There is no continuous retraction of the
disc `Dⁿ` onto its boundary sphere. (For `n = 0` the sphere is empty, so the statement
says only that `D⁰` is nonempty.) -/
theorem no_retraction (n : ℕ) :
    ¬ ∃ r : (Fin n → ℝ) → (Fin n → ℝ), ContinuousOn r (Disc n) ∧
      MapsTo r (Disc n) (Sphere n) ∧ ∀ x ∈ Sphere n, r x = x := by
  sorry

/-- **IOU (Brouwer's invariance of domain).** An injective continuous map from an open
subset of `ℝⁿ` to `ℝⁿ` has open image. -/
theorem invariance_of_domain {n : ℕ} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    {f : (Fin n → ℝ) → (Fin n → ℝ)} (hf : ContinuousOn f U) (hinj : InjOn f U) :
    IsOpen (f '' U) := by
  sorry

/-- **IOU (Jordan–Brouwer separation theorem).** The complement of an embedded
`(n-1)`-sphere in `Sⁿ` has exactly two components, and each has the sphere as its
frontier. Recall that `Sphere n` is `Sⁿ⁻¹` and `Sphere (n + 1)` is `Sⁿ`. -/
theorem jordan_brouwer_separation (n : ℕ) (g : Sphere n → Sphere (n + 1))
    (hg : IsEmbedding g) :
    ∃ U V : Set (Sphere (n + 1)), IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = (range g)ᶜ ∧ frontier U = range g ∧ frontier V = range g := by
  sorry

end DiscEmbedding

end
