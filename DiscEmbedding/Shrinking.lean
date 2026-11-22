/-
Copyright (c) 2026. Released under Apache 2.0 license.

# The Bing shrinking criterion (Book, Chapter 4)

We use the map formulation due to Edwards. For a continuous surjection `f : X → Y`
between compact metric spaces, the following are equivalent:

* `f` is *approximable by homeomorphisms*: for every `ε > 0` there is a homeomorphism
  `g : X ≃ₜ Y` with `dist (g x) (f x) < ε` for all `x`;
* `f` satisfies the *Bing shrinking criterion*: for every `ε > 0` there is a
  homeomorphism `h : X ≃ₜ X` such that `dist (f (h x)) (f x) < ε` for all `x`, and
  every point-inverse `f ⁻¹' {y}` is shrunk by `h` to diameter `< ε`.

The book phrases this via a decomposition `𝒟` of `X` and the quotient map
`X → X/𝒟`; for an upper semicontinuous decomposition of a compact metric space the
quotient is compact metrizable, so the two formulations agree.

Status: definitions and statement are in place; the easy direction
(approximable ⇒ shrinkable) is proved; the hard direction is `sorry`.
-/
module

public import DiscEmbedding.Basic

@[expose] public section

namespace DiscEmbedding

open Metric Set Function

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- `f` is a uniform limit of homeomorphisms `X ≃ₜ Y`. -/
def ApproximableByHomeomorphisms (f : X → Y) : Prop :=
  ∀ ε > 0, ∃ g : X ≃ₜ Y, ∀ x, dist (g x) (f x) < ε

/-- The Bing shrinking criterion for a map `f : X → Y`: point-inverses can be
simultaneously shrunk by a self-homeomorphism of `X` that moves points only slightly,
as measured in `Y`. -/
def SatisfiesBSC (f : X → Y) : Prop :=
  ∀ ε > 0, ∃ h : X ≃ₜ X,
    (∀ x, dist (f (h x)) (f x) < ε) ∧ ∀ y, diam (h '' (f ⁻¹' {y})) < ε

/-- Sanity check: a homeomorphism is approximable by homeomorphisms (by itself). -/
theorem Homeomorph.approximableByHomeomorphisms (e : X ≃ₜ Y) :
    ApproximableByHomeomorphisms e := fun ε hε => ⟨e, fun x => by simpa using hε⟩

/-- Sanity check: an injective map satisfies the shrinking criterion with `h = id`,
since all point-inverses are subsingletons. -/
theorem satisfiesBSC_of_injective {f : X → Y} (hf : Injective f) : SatisfiesBSC f := by
  intro ε hε
  refine ⟨Homeomorph.refl X, fun x => by simpa using hε, fun y => ?_⟩
  have hs : (f ⁻¹' {y}).Subsingleton := fun a ha b hb =>
    hf (by simp only [mem_preimage, mem_singleton_iff] at ha hb; rw [ha, hb])
  rw [diam_subsingleton (hs.image _)]
  exact hε

/-- The easy direction of the Bing shrinking criterion: a map approximable by
homeomorphisms satisfies the shrinking criterion.

Proof: take a homeomorphism `g` within `ε/2` of `f`, use uniform continuity of `g⁻¹`
to get `η`, take a second homeomorphism `g'` within `min (η/2) (ε/2)` of `f`, and set
`h = g⁻¹ ∘ g'`. -/
theorem ApproximableByHomeomorphisms.satisfiesBSC [CompactSpace Y] {f : X → Y}
    (hf : ApproximableByHomeomorphisms f) : SatisfiesBSC f := by
  intro ε hε
  obtain ⟨g, hg⟩ := hf (ε / 2) (by positivity)
  have hu : UniformContinuous g.symm :=
    CompactSpace.uniformContinuous_of_continuous g.symm.continuous
  obtain ⟨η, hη, hη'⟩ := Metric.uniformContinuous_iff.1 hu (ε / 2) (by positivity)
  obtain ⟨g', hg'⟩ := hf (min (η / 2) (ε / 2)) (by positivity)
  refine ⟨g'.trans g.symm, fun x => ?_, fun y => ?_⟩
  · have h1 : dist (f (g.symm (g' x))) (g' x) < ε / 2 := by
      have := hg (g.symm (g' x))
      rw [Homeomorph.apply_symm_apply] at this
      rwa [dist_comm]
    have h2 : dist (g' x) (f x) < ε / 2 := lt_of_lt_of_le (hg' x) (min_le_right _ _)
    calc dist (f ((g'.trans g.symm) x)) (f x)
        ≤ dist (f (g.symm (g' x))) (g' x) + dist (g' x) (f x) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add h1 h2
      _ = ε := add_halves ε
  · have hdiam : diam ((g'.trans g.symm) '' (f ⁻¹' {y})) ≤ ε / 2 := by
      apply Metric.diam_le_of_forall_dist_le (by positivity)
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [mem_preimage, mem_singleton_iff] at ha hb
      refine le_of_lt (hη' ?_)
      calc dist (g' a) (g' b) ≤ dist (g' a) y + dist y (g' b) := dist_triangle _ _ _
        _ < η / 2 + η / 2 := by
          refine add_lt_add ?_ ?_
          · rw [← ha]; exact lt_of_lt_of_le (hg' a) (min_le_left _ _)
          · rw [← hb, dist_comm]; exact lt_of_lt_of_le (hg' b) (min_le_left _ _)
        _ = η := add_halves η
    exact lt_of_le_of_lt hdiam (half_lt_self hε)

/-- **The Bing shrinking criterion** (Book, Chapter 4; Edwards' formulation).
A continuous surjection between compact metric spaces is approximable by homeomorphisms
if and only if it satisfies the shrinking criterion. -/
theorem bing_shrinking_criterion [CompactSpace X] [CompactSpace Y] (f : X → Y)
    (hf : Continuous f) (hsurj : Surjective f) :
    ApproximableByHomeomorphisms f ↔ SatisfiesBSC f := by
  refine ⟨ApproximableByHomeomorphisms.satisfiesBSC, fun h => ?_⟩
  -- The hard direction: build the approximating homeomorphisms as limits of
  -- compositions of shrinking homeomorphisms, using completeness of the space of
  -- self-maps of `X` with the sup metric. See blueprint, `thm:bsc-hard`.
  sorry

end DiscEmbedding

end
