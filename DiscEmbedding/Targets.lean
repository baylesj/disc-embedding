/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Long-range targets

The end goal of the project, stated now so that the definitions are forced early and
a topologist can check the statement before anyone spends effort on the proof.

* `poincare_four`: Freedman's topological 4-dimensional Poincaré conjecture.
* The disc embedding theorem itself is not yet stated formally: it needs generic
  immersions of discs, (equivariant) intersection numbers, framings and "good"
  fundamental groups, none of which exist in Mathlib. See blueprint, Part II.

A topological `n`-manifold is modelled as a Hausdorff, second-countable space with a
`ChartedSpace (Fin n → ℝ)` structure (charts are partial homeomorphisms onto open
subsets of `ℝⁿ`; no compatibility condition is needed in the `C⁰` setting).
-/
module

public import DiscEmbedding.Basic

@[expose] public section

namespace DiscEmbedding

/-- **Topological 4-dimensional Poincaré conjecture** (Freedman 1982).
A closed topological 4-manifold homotopy equivalent to `S⁴` is homeomorphic to `S⁴`.

Here `Sphere 5 ⊆ Fin 5 → ℝ` is the 4-sphere. We assume compactness and second
countability explicitly; this matches the usual statement ("closed 4-manifold") and is
slightly weaker than Mathlib's `proof_wanted`, which assumes only Hausdorffness. -/
theorem poincare_four (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M] [ChartedSpace (Fin 4 → ℝ) M]
    (h : ContinuousMap.HomotopyEquiv M (Sphere 5)) :
    Nonempty (M ≃ₜ Sphere 5) := by
  sorry

end DiscEmbedding

end
