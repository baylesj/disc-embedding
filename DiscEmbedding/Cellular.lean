/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Cellular sets shrink (Book, Chapter 3)

If `A` is a cellular subset of a metric space `M` and `q : M → Y` collapses exactly `A`
to a point, then `q` satisfies the Bing shrinking criterion. Combined with
`bing_shrinking_criterion`, this gives `M/A ≅ M` whenever `M` is compact.

Proof: given `ε`, pick a ball `Bᵢ = eᵢ(Dⁿ)` so small that `q(Bᵢ)` lies within `ε/2` of the
collapse point. Inside `Bᵢ`, the set `A` sits in `eᵢ` of a closed `r`-ball with `r < 1`.
Transplant the radial squeeze of `ℝⁿ` that is the identity outside `Dⁿ` and maps the
`r`-ball into a tiny `δ`-ball. The resulting homeomorphism of `M` moves points only inside
`Bᵢ`, so it barely moves them as seen from `Y`, and it shrinks `A` to diameter `< ε`.
-/
module

public import DiscEmbedding.Shrinking
public import DiscEmbedding.Squeeze

@[expose] public section

namespace DiscEmbedding

open Metric Set Function Filter Topology

/-- **Cellular sets shrink.** If `A ⊆ M` is cellular and `q : M → Y` collapses exactly
`A` to the point `p`, being injective elsewhere, then `q` satisfies the Bing shrinking
criterion. -/
theorem IsCellular.satisfiesBSC_of_collapse {M Y : Type*} [MetricSpace M] [MetricSpace Y]
    {n : ℕ} {A : Set M} (hA : IsCellular n A) {q : M → Y} (hq : Continuous q) {p : Y}
    (hqA : q ⁻¹' {p} = A) (hsub : ∀ y ≠ p, (q ⁻¹' {y}).Subsingleton) : SatisfiesBSC q := by
  obtain ⟨e, he, hnest, rfl⟩ := hA
  have hBc : ∀ i, IsCompact (e i '' closedBall (0 : Fin n → ℝ) 1) := fun i =>
    (isCompact_closedBall _ _).image (he i).continuous
  have hBanti : Antitone fun i => e i '' closedBall (0 : Fin n → ℝ) 1 :=
    antitone_nat_of_succ_le fun i => (hnest i).trans (image_mono ball_subset_closedBall)
  intro ε hε
  -- Step 1: choose a ball `Bᵢ` whose image under `q` is within `ε/2` of `p`.
  have hUopen : IsOpen (q ⁻¹' ball p (ε / 2)) := isOpen_ball.preimage hq
  have hAU : (⋂ i, e i '' closedBall (0 : Fin n → ℝ) 1) ⊆ q ⁻¹' ball p (ε / 2) := by
    intro x hx
    have hqx : q x = p := by rw [← hqA] at hx; exact hx
    show q x ∈ ball p (ε / 2)
    rw [hqx]
    exact mem_ball_self (by positivity)
  obtain ⟨i, hi⟩ :=
    exists_subset_nhds_of_isCompact hBanti.directed_ge hBc (hUopen.mem_nhdsSet.2 hAU)
  -- Step 2: in the coordinates of `eᵢ`, the next ball (hence `A`) lies in an `r`-ball.
  let K : Set (Fin n → ℝ) := e i ⁻¹' (e (i + 1) '' closedBall 0 1)
  have hKc : IsCompact K :=
    (he i).isInducing.isCompact_preimage' (hBc (i + 1))
      ((hnest i).trans (image_subset_range _ _))
  have hKball : K ⊆ ball 0 1 := fun z hz => by
    obtain ⟨w, hw, hwz⟩ := hnest i hz
    rwa [← (he i).injective hwz]
  obtain ⟨r, hr0, hr1, hKr⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ K ⊆ closedBall 0 r := by
    rcases K.eq_empty_or_nonempty with hK | hK
    · exact ⟨1 / 2, by norm_num, by norm_num, by simp [hK]⟩
    · obtain ⟨z₀, hz₀, hmax⟩ := hKc.exists_isMaxOn hK continuous_norm.continuousOn
      have hz₀1 : ‖z₀‖ < 1 := mem_ball_zero_iff.1 (hKball hz₀)
      refine ⟨max ‖z₀‖ (1 / 2), by positivity, max_lt hz₀1 (by norm_num), fun z hz => ?_⟩
      rw [mem_closedBall_zero_iff]
      exact (isMaxOn_iff.1 hmax z hz).trans (le_max_left _ _)
  -- Step 3: choose `δ` so that `eᵢ` maps the `δ`-ball into a small ball of `M`.
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ :=
    Metric.continuousAt_iff.1 (he i).continuous.continuousAt (ε / 3) (by positivity)
  set δ := min (δ₀ / 2) (r / 2) with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδr : δ < r := (min_le_right _ _).trans_lt (by linarith)
  have hδδ₀ : δ < δ₀ := (min_le_left _ _).trans_lt (by linarith)
  -- Step 4: transplant the radial squeeze through `eᵢ`.
  let σ : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) := squeezeHomeomorph hδ0 hδr hr1
  have hσfix : ∀ x ∉ closedBall (0 : Fin n → ℝ) 1, σ x = x := fun x hx =>
    squeezeHomeomorph_eq_self hδ0 hδr hr1
      (le_of_lt (not_le.1 fun h => hx (mem_closedBall_zero_iff.2 h)))
  let h : M ≃ₜ M := transplant (he i) σ (isCompact_closedBall 0 1) hσfix
  refine ⟨h, fun x => ?_, fun y => ?_⟩
  · -- `h` moves points only inside `Bᵢ`, whose image under `q` is near `p`.
    by_cases hx : x ∈ e i '' closedBall 0 1
    · obtain ⟨z, hz, rfl⟩ := hx
      have hσz : σ z ∈ closedBall (0 : Fin n → ℝ) 1 :=
        mem_closedBall_zero_iff.2
          (norm_squeezeHomeomorph_le_one hδ0 hδr hr1 (mem_closedBall_zero_iff.1 hz))
      have h1 : q (e i (σ z)) ∈ ball p (ε / 2) := hi (mem_image_of_mem _ hσz)
      have h2 : q (e i z) ∈ ball p (ε / 2) := hi (mem_image_of_mem _ hz)
      rw [show h (e i z) = e i (σ z) from transplant_apply (he i) σ _ hσfix z]
      calc dist (q (e i (σ z))) (q (e i z))
          ≤ dist (q (e i (σ z))) p + dist p (q (e i z)) := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add (mem_ball.1 h1) (by rw [dist_comm]; exact mem_ball.1 h2)
        _ = ε := add_halves ε
    · rw [show h x = x from transplant_eq_self (he i) σ _ hσfix hx, dist_self]
      exact hε
  · by_cases hy : y = p
    · -- The fiber over `p` is `A`, which `h` squeezes into a small ball.
      rw [hy, hqA]
      have hsub' : h '' (⋂ i, e i '' closedBall (0 : Fin n → ℝ) 1) ⊆
          closedBall (e i 0) (ε / 3) := by
        rintro _ ⟨x, hx, rfl⟩
        have hx1 : x ∈ e (i + 1) '' closedBall 0 1 := mem_iInter.1 hx (i + 1)
        obtain ⟨z, -, rfl⟩ := hnest i hx1
        have hzK : z ∈ K := hx1
        have hσz : ‖σ z‖ ≤ δ :=
          norm_squeezeHomeomorph_le hδ0 hδr hr1 (mem_closedBall_zero_iff.1 (hKr hzK))
        rw [show h (e i z) = e i (σ z) from transplant_apply (he i) σ _ hσfix z,
          mem_closedBall]
        refine le_of_lt (hδ₀' ?_)
        rw [dist_zero_right]
        exact hσz.trans_lt hδδ₀
      calc diam (h '' (⋂ i, e i '' closedBall (0 : Fin n → ℝ) 1)) ≤ 2 * (ε / 3) :=
            diam_le_of_subset_closedBall (by positivity) hsub'
        _ < ε := by linarith
    · -- Every other fiber is a single point.
      rw [diam_subsingleton ((hsub y hy).image _)]
      exact hε

/-- If `M` is compact, collapsing a cellular set does not change `M` up to
homeomorphism: the collapse map is approximable by homeomorphisms. -/
theorem IsCellular.approximableByHomeomorphisms_of_collapse {M Y : Type*} [MetricSpace M]
    [MetricSpace Y] [CompactSpace M] [CompactSpace Y] {n : ℕ} {A : Set M}
    (hA : IsCellular n A) {q : M → Y} (hq : Continuous q) (hsurj : Surjective q) {p : Y}
    (hqA : q ⁻¹' {p} = A) (hsub : ∀ y ≠ p, (q ⁻¹' {y}).Subsingleton) :
    ApproximableByHomeomorphisms q :=
  SatisfiesBSC.approximableByHomeomorphisms hq hsurj (hA.satisfiesBSC_of_collapse hq hqA hsub)

end DiscEmbedding

end
