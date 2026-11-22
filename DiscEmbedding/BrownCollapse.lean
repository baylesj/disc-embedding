/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Brown's Theorem 1: collapsing a cellular set inside a cell

If `M` is a cellular subset of the open cube in `ℝⁿ`, there is a continuous surjection
`g : ℝⁿ → ℝⁿ`, equal to the identity outside the open cube, that collapses `M` to a
point and is injective everywhere else.

Construction (Brown 1960, Theorem 1): let `Bₖ` be the collared balls with `⋂ Bₖ = M`. Set
`h₀ = id` and `hₖ₊₁ = hₖ ∘ τₖ`, where `τₖ` is a homeomorphism supported in `Bₖ` that
maps `Bₖ` into itself and squeezes `Bₖ₊₁` so that `hₖ₊₁(Bₖ₊₁)` has diameter `< 1/(k+1)`.
Then `hⱼ(Bₖ) ⊆ hₖ(Bₖ)` for `j ≥ k`, so the `hₖ` converge uniformly to the map we want.
-/
module

public import DiscEmbedding.Cellular

@[expose] public section

namespace DiscEmbedding

open Metric Set Function Filter Topology

/-- A compact subset of the open unit ball lies in a closed ball of radius `r < 1`. -/
theorem exists_radius_of_isCompact {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hK1 : K ⊆ ball 0 1) : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ K ⊆ closedBall 0 r := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨1 / 2, by norm_num, by norm_num, by simp [hKe]⟩
  · obtain ⟨z₀, hz₀, hmax⟩ := hK.exists_isMaxOn hKne continuous_norm.continuousOn
    have hz₀1 : ‖z₀‖ < 1 := mem_ball_zero_iff.1 (hK1 hz₀)
    refine ⟨max ‖z₀‖ (1 / 2), by positivity, max_lt hz₀1 (by norm_num), fun z hz => ?_⟩
    rw [mem_closedBall_zero_iff]
    exact (isMaxOn_iff.1 hmax z hz).trans (le_max_left _ _)

/-- **One squeezing step.** Given a collared ball `B = e(Dⁿ)`, a compact `B' ⊆ e(int Dⁿ)`,
and a continuous map `H`, there is a homeomorphism `τ` supported in `B`, mapping `B` into
itself, such that `H(τ(B'))` has diameter `< ε`. -/
theorem exists_squeeze_step {n : ℕ} {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {e : (Fin n → ℝ) → X} (he : IsOpenEmbedding e) {B' : Set X} (hB' : IsCompact B')
    (hB'sub : B' ⊆ e '' ball 0 1) {H : X → Y} (hH : Continuous H) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : X ≃ₜ X, (∀ x ∉ e '' closedBall 0 1, τ x = x) ∧
      MapsTo τ (e '' closedBall 0 1) (e '' closedBall 0 1) ∧ diam (H '' (τ '' B')) < ε := by
  let K : Set (Fin n → ℝ) := e ⁻¹' B'
  have hKc : IsCompact K :=
    he.isInducing.isCompact_preimage' hB' (hB'sub.trans (image_subset_range _ _))
  have hKball : K ⊆ ball 0 1 := fun z hz => by
    obtain ⟨w, hw, hwz⟩ := hB'sub hz
    rwa [← he.injective hwz]
  obtain ⟨r, hr0, hr1, hKr⟩ := exists_radius_of_isCompact hKc hKball
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ :=
    Metric.continuousAt_iff.1 (hH.comp he.continuous).continuousAt (ε / 3) (by positivity)
  set δ := min (δ₀ / 2) (r / 2)
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδr : δ < r := (min_le_right _ _).trans_lt (by linarith)
  have hδδ₀ : δ < δ₀ := (min_le_left _ _).trans_lt (by linarith)
  let σ : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) := squeezeHomeomorph hδ0 hδr hr1
  have hσfix : ∀ x ∉ closedBall (0 : Fin n → ℝ) 1, σ x = x := fun x hx =>
    squeezeHomeomorph_eq_self hδ0 hδr hr1
      (le_of_lt (not_le.1 fun h => hx (mem_closedBall_zero_iff.2 h)))
  refine ⟨transplant he σ (isCompact_closedBall 0 1) hσfix, fun x hx => ?_, ?_, ?_⟩
  · exact transplant_eq_self he σ _ hσfix hx
  · rintro _ ⟨z, hz, rfl⟩
    rw [transplant_apply he σ _ hσfix z]
    exact mem_image_of_mem _ (mem_closedBall_zero_iff.2
      (norm_squeezeHomeomorph_le_one hδ0 hδr hr1 (mem_closedBall_zero_iff.1 hz)))
  · have hsub : H '' (transplant he σ (isCompact_closedBall 0 1) hσfix '' B') ⊆
        closedBall (H (e 0)) (ε / 3) := by
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      obtain ⟨z, -, rfl⟩ := hB'sub hx
      have hzK : z ∈ K := hx
      have hσz : ‖σ z‖ ≤ δ :=
        norm_squeezeHomeomorph_le hδ0 hδr hr1 (mem_closedBall_zero_iff.1 (hKr hzK))
      rw [transplant_apply he σ _ hσfix z, mem_closedBall]
      refine le_of_lt (hδ₀' ?_)
      rw [dist_zero_right]
      exact hσz.trans_lt hδδ₀
    calc diam (H '' (transplant he σ (isCompact_closedBall 0 1) hσfix '' B')) ≤ 2 * (ε / 3) :=
          diam_le_of_subset_closedBall (by positivity) hsub
      _ < ε := by linarith

/-- **Brown's Theorem 1.** A cellular subset `M` of the open cube can be collapsed to a
point by a continuous surjection of `ℝⁿ` that is the identity outside the open cube
and injective away from `M`. -/
theorem brown_collapse_cellular {n : ℕ} {M : Set (Fin n → ℝ)} (hM : IsCellular n M)
    (hMQ : M ⊆ ball 0 1) :
    ∃ g : (Fin n → ℝ) → (Fin n → ℝ), Continuous g ∧ Surjective g ∧
      (∀ x ∉ ball (0 : Fin n → ℝ) 1, g x = x) ∧
      ∃ p, g ⁻¹' {p} = M ∧ ∀ y ≠ p, (g ⁻¹' {y}).Subsingleton := by
  obtain ⟨e, he, hnest, rfl⟩ := hM
  have hBc0 : ∀ i, IsCompact (e i '' closedBall (0 : Fin n → ℝ) 1) := fun i =>
    (isCompact_closedBall _ _).image (he i).continuous
  have hBanti0 : Antitone fun i => e i '' closedBall (0 : Fin n → ℝ) 1 :=
    antitone_nat_of_succ_le fun i => (hnest i).trans (image_mono ball_subset_closedBall)
  obtain ⟨i₀, hi₀⟩ := exists_subset_nhds_of_isCompact hBanti0.directed_ge hBc0
    (isOpen_ball.mem_nhdsSet.2 hMQ)
  -- Reindex so that the first ball lies in the open cube.
  set E : ℕ → (Fin n → ℝ) → (Fin n → ℝ) := fun k => e (i₀ + k) with hEdef
  set B : ℕ → Set (Fin n → ℝ) := fun k => E k '' closedBall 0 1 with hBdef
  have hE : ∀ k, IsOpenEmbedding (E k) := fun k => he _
  have hEnest : ∀ k, B (k + 1) ⊆ E k '' ball 0 1 := fun k => hnest (i₀ + k)
  have hBc : ∀ k, IsCompact (B k) := fun k => hBc0 _
  have hBsucc : ∀ k, B (k + 1) ⊆ B k := fun k =>
    (hEnest k).trans (image_mono ball_subset_closedBall)
  have hBanti : Antitone B := antitone_nat_of_succ_le hBsucc
  have hB0 : B 0 ⊆ ball 0 1 := hi₀
  have hMeq : (⋂ i, e i '' closedBall (0 : Fin n → ℝ) 1) = ⋂ k, B k := by
    apply Subset.antisymm
    · exact subset_iInter fun k => iInter_subset _ (i₀ + k)
    · refine subset_iInter fun i => (iInter_subset _ i).trans ?_
      exact hBanti0 (Nat.le_add_left i i₀)
  rw [hMeq]
  set M := ⋂ k, B k with hMdef
  -- The sequence of homeomorphisms.
  have hstep : ∀ (k : ℕ) (H : (Fin n → ℝ) ≃ₜ (Fin n → ℝ)), ∃ τ : (Fin n → ℝ) ≃ₜ (Fin n → ℝ),
      (∀ x ∉ B k, τ x = x) ∧ MapsTo τ (B k) (B k) ∧ diam (H '' (τ '' B (k + 1))) < 1 / (k + 1) :=
    fun k H => exists_squeeze_step (hE k) (hBc (k + 1)) (hEnest k) H.continuous
      (by positivity)
  choose τ hτfix hτmaps hτdiam using hstep
  let h : ℕ → (Fin n → ℝ) ≃ₜ (Fin n → ℝ) := fun k =>
    Nat.rec (Homeomorph.refl _) (fun k hk => (τ k hk).trans hk) k
  have hsucc : ∀ k x, h (k + 1) x = h k (τ k (h k) x) := fun _ _ => rfl
  have h0 : ∀ x, h 0 x = x := fun _ => rfl
  -- Points outside `Bₖ` are not moved after stage `k`.
  have hF3 : ∀ k j, k ≤ j → ∀ x ∉ B k, h j x = h k x := by
    intro k j hkj x hx
    induction j, hkj using Nat.le_induction with
    | base => rfl
    | succ j hkj ih =>
      rw [hsucc, hτfix j (h j) x (fun hxj => hx (hBanti hkj hxj)), ih]
  -- Points of `Bₖ` stay in `hₖ(Bₖ)`.
  have hF2 : ∀ k j, k ≤ j → ∀ x ∈ B k, h j x ∈ h k '' B k := by
    intro k j hkj
    induction j, hkj using Nat.le_induction with
    | base => exact fun x hx => mem_image_of_mem _ hx
    | succ j hkj ih =>
      intro x hx
      rw [hsucc]
      by_cases hxj : x ∈ B j
      · exact ih _ (hBanti hkj (hτmaps j (h j) hxj))
      · rw [hτfix j (h j) x hxj]
        exact ih x hx
  set d : ℕ → ℝ := fun k => diam (h k '' B k) with hddef
  have hbdd : ∀ k, Bornology.IsBounded (h k '' B k) := fun k =>
    ((hBc k).image (h k).continuous).isBounded
  have hd : ∀ k, d (k + 1) < 1 / (k + 1) := by
    intro k
    have : h (k + 1) '' B (k + 1) = h k '' (τ k (h k) '' B (k + 1)) :=
      (image_image (h k) (τ k (h k)) (B (k + 1))).symm
    simp only [hddef]
    rw [this]
    exact hτdiam k (h k)
  have hF5 : ∀ k j x, k ≤ j → dist (h j x) (h k x) ≤ d k := by
    intro k j x hkj
    by_cases hx : x ∈ B k
    · exact dist_le_diam_of_mem (hbdd k) (hF2 k j hkj x hx) (mem_image_of_mem _ hx)
    · rw [hF3 k j hkj x hx, dist_self]
      exact diam_nonneg
  -- Pointwise limit.
  have hcauchy : ∀ x, CauchySeq fun j => h j x := by
    intro x
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    exact ⟨k + 1, fun j hj => (hF5 (k + 1) j x hj).trans_lt ((hd k).trans hk)⟩
  let g : (Fin n → ℝ) → (Fin n → ℝ) := fun x => limUnder atTop fun j => h j x
  have hlim : ∀ x, Tendsto (fun j => h j x) atTop (𝓝 (g x)) := fun x =>
    (hcauchy x).tendsto_limUnder
  have hbound : ∀ k x, dist (g x) (h k x) ≤ d k := by
    intro k x
    refine le_of_tendsto ((hlim x).dist tendsto_const_nhds) ?_
    exact eventually_atTop.2 ⟨k, fun j hj => hF5 k j x hj⟩
  have hg_out : ∀ k x, x ∉ B k → g x = h k x := by
    intro k x hx
    refine tendsto_nhds_unique (hlim x) ?_
    exact tendsto_const_nhds.congr' (eventually_atTop.2 ⟨k, fun j hj => (hF3 k j hj x hx).symm⟩)
  have hg_in : ∀ k x, x ∈ B k → g x ∈ h k '' B k := by
    intro k x hx
    exact ((hBc k).image (h k).continuous).isClosed.mem_of_tendsto (hlim x)
      (eventually_atTop.2 ⟨k, fun j hj => hF2 k j hj x hx⟩)
  -- Continuity: the convergence is uniform.
  have hunif : TendstoUniformly (fun j x => h j x) g atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    refine eventually_atTop.2 ⟨k + 1, fun j hj x => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    have hmk : (1 : ℝ) / (m + 1) ≤ 1 / (k + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast (by omega : k + 1 ≤ m + 1)
    exact (hbound (m + 1) x).trans_lt ((hd m).trans_le hmk |>.trans hk)
  have hgc : Continuous g :=
    hunif.continuous (Frequently.of_forall fun j => (h j).continuous)
  -- `g` is the identity outside the open cube.
  have hg_fix : ∀ x ∉ ball (0 : Fin n → ℝ) 1, g x = x := fun x hx => by
    rw [hg_out 0 x (fun h' => hx (hB0 h')), h0]
  -- Injectivity away from `M`.
  have hinj : ∀ x y, x ∉ M → x ≠ y → g x ≠ g y := by
    intro x y hx hxy hgxy
    obtain ⟨k, hk⟩ : ∃ k, x ∉ B k := by simpa [hMdef] using hx
    rw [hg_out k x hk] at hgxy
    by_cases hy : y ∈ B k
    · obtain ⟨z, hz, hzy⟩ := hg_in k y hy
      rw [← hgxy] at hzy
      exact hk ((h k).injective hzy ▸ hz)
    · rw [hg_out k y hy] at hgxy
      exact hxy ((h k).injective hgxy)
  -- `g` is constant on `M`.
  have hconst : ∀ x ∈ M, ∀ y ∈ M, g x = g y := by
    intro x hx y hy
    by_contra hne
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (dist_pos.2 hne)
    have hxk : x ∈ B (k + 1) := mem_iInter.1 hx (k + 1)
    have hyk : y ∈ B (k + 1) := mem_iInter.1 hy (k + 1)
    have := dist_le_diam_of_mem (hbdd (k + 1)) (hg_in _ x hxk) (hg_in _ y hyk)
    linarith [hd k]
  -- `M` is nonempty.
  obtain ⟨m₀, hm₀⟩ : M.Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed B hBsucc
      (fun k => ⟨E k 0, mem_image_of_mem _ (mem_closedBall_self zero_le_one)⟩) (hBc 0)
      (fun k => (hBc k).isClosed)
  refine ⟨g, hgc, ?_, hg_fix, g m₀, ?_, ?_⟩
  · -- Surjectivity: `g` is a uniform limit of surjections.
    intro y
    by_cases hy : y ∈ ball (0 : Fin n → ℝ) 1
    · have hcl : IsClosed (g '' closedBall 0 1) :=
        ((isCompact_closedBall 0 1).image hgc).isClosed
      have hmem : y ∈ closure (g '' closedBall 0 1) := by
        rw [Metric.mem_closure_iff]
        intro ε hε
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
        set x := (h (k + 1)).symm y
        have hx1 : x ∈ closedBall (0 : Fin n → ℝ) 1 := by
          by_contra hx
          have hxb : x ∉ B 0 := fun h' => hx (ball_subset_closedBall (hB0 h'))
          have := hF3 0 (k + 1) (Nat.zero_le _) x hxb
          rw [h0, Homeomorph.apply_symm_apply] at this
          exact hx (this ▸ ball_subset_closedBall hy)
        refine ⟨g x, mem_image_of_mem _ hx1, ?_⟩
        have := hbound (k + 1) x
        rw [Homeomorph.apply_symm_apply] at this
        rw [dist_comm]
        exact this.trans_lt ((hd k).trans hk)
      obtain ⟨x, -, hx⟩ := hcl.closure_eq ▸ hmem
      exact ⟨x, hx⟩
    · exact ⟨y, hg_fix y hy⟩
  · ext x
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro hgx
      by_contra hx
      exact hinj x m₀ hx (fun h' => hx (h' ▸ hm₀)) hgx
    · intro hx
      exact hconst x hx m₀ hm₀
  · intro y hy a ha b hb
    simp only [mem_preimage, mem_singleton_iff] at ha hb
    have haM : a ∉ M := fun h' => hy (ha ▸ hconst a h' m₀ hm₀)
    by_contra hab
    exact hinj a b haM hab (ha.trans hb.symm)

end DiscEmbedding

end
