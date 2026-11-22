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

Status: both directions are proved. The hard direction (shrinkable ⇒ approximable)
uses the Baire category theorem in the space `C(X, Y)` with the sup metric.
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

/-! ### The hard direction

Let `A` be the closure, in `C(X, Y)` with the sup metric, of `{f ∘ h | h : X ≃ₜ X}`.
It is a closed subset of a complete space, hence a Baire space. For each `n`, the maps
that separate any two points at distance `≥ 1/(n+1)` form an open subset of `A`, and the
shrinking criterion makes it dense. A map in the (dense) intersection that is close to
`f` is injective, and every map in `A` is surjective, so it is a homeomorphism.
-/

section HardDirection

variable [CompactSpace X] [CompactSpace Y]

/-- Continuous maps that send any two points at distance `≥ 1/(n+1)` to different
points. -/
def SeparatesAtScale (n : ℕ) : Set C(X, Y) :=
  {g | ∀ x x', 1 / ((n : ℝ) + 1) ≤ dist x x' → g x ≠ g x'}

omit [CompactSpace Y] in
theorem isOpen_separatesAtScale (n : ℕ) :
    IsOpen (SeparatesAtScale (X := X) (Y := Y) n) := by
  rw [Metric.isOpen_iff]
  intro g hg
  set K : Set (X × X) := {p | 1 / ((n : ℝ) + 1) ≤ dist p.1 p.2} with hKdef
  have hK : IsCompact K := (isClosed_le continuous_const continuous_dist).isCompact
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, one_pos, fun g' _ x x' hxx' _ => ?_⟩
    have hmem : (x, x') ∈ K := hxx'
    rw [hKe] at hmem
    exact hmem
  · have hcont : Continuous (fun p : X × X => dist (g p.1) (g p.2)) := by fun_prop
    obtain ⟨p₀, hp₀K, hmin⟩ := hK.exists_isMinOn hKne hcont.continuousOn
    have hc : 0 < dist (g p₀.1) (g p₀.2) := dist_pos.2 (hg p₀.1 p₀.2 hp₀K)
    refine ⟨dist (g p₀.1) (g p₀.2) / 2, by positivity, fun g' hg' x x' hxx' heq => ?_⟩
    have h1 : dist (g p₀.1) (g p₀.2) ≤ dist (g x) (g x') :=
      isMinOn_iff.1 hmin (x, x') hxx'
    have h2 : dist (g' x) (g x) < dist (g p₀.1) (g p₀.2) / 2 :=
      lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist x) (mem_ball.1 hg')
    have h3 : dist (g' x') (g x') < dist (g p₀.1) (g p₀.2) / 2 :=
      lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist x') (mem_ball.1 hg')
    have h4 : dist (g' x) (g x') = dist (g' x') (g x') := by rw [heq]
    have h5 := dist_triangle (g x) (g' x) (g x')
    rw [dist_comm (g x) (g' x), h4] at h5
    linarith

/-- **The hard direction of the Bing shrinking criterion.** -/
theorem SatisfiesBSC.approximableByHomeomorphisms {f : X → Y} (hf : Continuous f)
    (hsurj : Surjective f) (hB : SatisfiesBSC f) : ApproximableByHomeomorphisms f := by
  intro ε hε
  let F : C(X, Y) := ⟨f, hf⟩
  let S : Set C(X, Y) := range fun h : X ≃ₜ X => F.comp (h : C(X, X))
  let A : Set C(X, Y) := closure S
  -- Step 1: every map in `A` is surjective.
  have hA_surj : ∀ g ∈ A, Surjective g := by
    intro g hg y
    show y ∈ range g
    rw [← (isCompact_range g.continuous).isClosed.closure_eq, Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨s, ⟨h, rfl⟩, hs⟩ := Metric.mem_closure_iff.1 hg δ hδ
    obtain ⟨x, hx⟩ := hsurj y
    refine ⟨g (h.symm x), mem_range_self _, ?_⟩
    have hy : (F.comp (h : C(X, X))) (h.symm x) = y := by
      show f (h (h.symm x)) = y
      rw [Homeomorph.apply_symm_apply, hx]
    calc dist y (g (h.symm x))
        = dist ((F.comp (h : C(X, X))) (h.symm x)) (g (h.symm x)) := by rw [hy]
      _ ≤ dist (F.comp (h : C(X, X))) g := ContinuousMap.dist_apply_le_dist _
      _ < δ := by rwa [dist_comm]
  -- Step 2: maps in `S` separating at scale `1/(n+1)` are dense in `A`.
  have hdense : ∀ n : ℕ, ∀ g ∈ A, ∀ δ > 0,
      ∃ s ∈ S, s ∈ SeparatesAtScale n ∧ dist s g < δ := by
    intro n g hg δ hδ
    obtain ⟨s, ⟨h, rfl⟩, hs⟩ := Metric.mem_closure_iff.1 hg (δ / 2) (by positivity)
    have hu : UniformContinuous h.symm :=
      CompactSpace.uniformContinuous_of_continuous h.symm.continuous
    obtain ⟨η, hη, hη'⟩ :=
      Metric.uniformContinuous_iff.1 hu (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨k, hk1, hk2⟩ := hB (min η (δ / 2)) (by positivity)
    refine ⟨F.comp ((h.trans k.symm : X ≃ₜ X) : C(X, X)), ⟨h.trans k.symm, rfl⟩, ?_, ?_⟩
    · intro x x' hxx' heq
      have heq' : f (k.symm (h x)) = f (k.symm (h x')) := heq
      have hx : h x ∈ k '' (f ⁻¹' {f (k.symm (h x))}) :=
        ⟨k.symm (h x), mem_singleton _, k.apply_symm_apply _⟩
      have hx' : h x' ∈ k '' (f ⁻¹' {f (k.symm (h x))}) :=
        ⟨k.symm (h x'), heq'.symm, k.apply_symm_apply _⟩
      have hd : dist (h x) (h x') < η :=
        lt_of_le_of_lt (dist_le_diam_of_mem isBounded_of_compactSpace hx hx')
          (lt_of_lt_of_le (hk2 _) (min_le_left _ _))
      have := hη' hd
      simp only [Homeomorph.symm_apply_apply] at this
      linarith
    · have hfirst : dist (F.comp ((h.trans k.symm : X ≃ₜ X) : C(X, X)))
          (F.comp (h : C(X, X))) ≤ δ / 2 := by
        refine (ContinuousMap.dist_le (by positivity)).2 fun x => ?_
        show dist (f (k.symm (h x))) (f (h x)) ≤ δ / 2
        have := hk1 (k.symm (h x))
        rw [Homeomorph.apply_symm_apply, dist_comm] at this
        exact le_of_lt (lt_of_lt_of_le this (min_le_right _ _))
      calc dist (F.comp ((h.trans k.symm : X ≃ₜ X) : C(X, X))) g
          ≤ dist (F.comp ((h.trans k.symm : X ≃ₜ X) : C(X, X))) (F.comp (h : C(X, X)))
            + dist (F.comp (h : C(X, X))) g := dist_triangle _ _ _
        _ < δ / 2 + δ / 2 := add_lt_add_of_le_of_lt hfirst (by rwa [dist_comm])
        _ = δ := add_halves δ
  -- Step 3: Baire category in the complete space `A`.
  have : CompleteSpace A := completeSpace_coe_iff_isComplete.2 isClosed_closure.isComplete
  let W : ℕ → Set A := fun n => ((↑) : A → C(X, Y)) ⁻¹' SeparatesAtScale n
  have hWo : ∀ n, IsOpen (W n) := fun n =>
    (isOpen_separatesAtScale n).preimage continuous_subtype_val
  have hWd : ∀ n, Dense (W n) := by
    intro n
    rw [Metric.dense_iff]
    intro a r hr
    obtain ⟨s, hsS, hsV, hsd⟩ := hdense n a a.2 r hr
    exact ⟨⟨s, subset_closure hsS⟩, hsd, hsV⟩
  have hD := dense_iInter_of_isOpen_nat hWo hWd
  have hFA : F ∈ A := subset_closure ⟨Homeomorph.refl X, rfl⟩
  obtain ⟨a, haball, haW⟩ := Metric.dense_iff.1 hD ⟨F, hFA⟩ ε hε
  -- Step 4: the map `a` is a homeomorphism close to `f`.
  have hinj : Injective (a : C(X, Y)) := by
    intro x x' hxx
    by_contra hne
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (dist_pos.2 hne)
    exact (mem_iInter.1 haW n) x x' hn.le hxx
  let e : X ≃ Y := Equiv.ofBijective (a : C(X, Y)) ⟨hinj, hA_surj a a.2⟩
  refine ⟨Continuous.homeoOfEquivCompactToT2 (f := e) (a : C(X, Y)).continuous,
    fun x => ?_⟩
  show dist ((a : C(X, Y)) x) (F x) < ε
  exact lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist x) haball

end HardDirection

/-- **The Bing shrinking criterion** (Book, Chapter 4; Edwards' formulation).
A continuous surjection between compact metric spaces is approximable by homeomorphisms
if and only if it satisfies the shrinking criterion. -/
theorem bing_shrinking_criterion [CompactSpace X] [CompactSpace Y] (f : X → Y)
    (hf : Continuous f) (hsurj : Surjective f) :
    ApproximableByHomeomorphisms f ↔ SatisfiesBSC f :=
  ⟨ApproximableByHomeomorphisms.satisfiesBSC, SatisfiesBSC.approximableByHomeomorphisms hf hsurj⟩

end DiscEmbedding

end
