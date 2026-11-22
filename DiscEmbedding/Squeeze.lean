/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Squeezing homeomorphisms

Two pieces of machinery used to shrink cellular sets (Book, Chapter 3):

* `squeezeHomeomorph δ r`: a radial homeomorphism of a real normed space that is the
  identity outside the closed unit ball and maps the closed `r`-ball into the closed
  `δ`-ball. It rescales each vector so that its norm `t` becomes `squeezeFun δ r t`, the
  piecewise-linear function through `(0, 0)`, `(r, δ)` and `(1, 1)` with slope `1`
  beyond `1`.
* `transplant e σ`: given an open embedding `e : E → M` and a homeomorphism `σ` of `E`
  that is the identity outside a compact set `K`, the homeomorphism of `M` that is
  `e ∘ σ ∘ e⁻¹` on the image of `e` and the identity elsewhere.
-/
module

public import DiscEmbedding.Basic

@[expose] public section

namespace DiscEmbedding

open Metric Set Function Filter Topology

/-! ### Radial homeomorphisms -/

section Radial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Rescale `x` along its ray so that its norm becomes `ρ ‖x‖`. -/
noncomputable def radialFun (ρ : ℝ → ℝ) (x : E) : E := (ρ ‖x‖ / ‖x‖) • x

theorem radialFun_zero (ρ : ℝ → ℝ) : radialFun ρ (0 : E) = 0 := by simp [radialFun]

theorem norm_radialFun {ρ : ℝ → ℝ} (hρ : ∀ t, 0 ≤ t → 0 ≤ ρ t) (hρ0 : ρ 0 = 0) (x : E) :
    ‖radialFun ρ x‖ = ρ ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx, radialFun, hρ0]
  · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    rw [radialFun, norm_smul, Real.norm_of_nonneg (div_nonneg (hρ _ hn.le) hn.le),
      div_mul_cancel₀ _ hn.ne']

theorem radialFun_eq_self {ρ : ℝ → ℝ} {x : E} (h : ρ ‖x‖ = ‖x‖) : radialFun ρ x = x := by
  by_cases hx : x = 0
  · simp [hx, radialFun]
  · rw [radialFun, h, div_self (norm_ne_zero_iff.2 hx), one_smul]

theorem continuous_radialFun {ρ : ℝ → ℝ} (hρc : Continuous ρ) (hρ : ∀ t, 0 ≤ t → 0 ≤ ρ t)
    (hρ0 : ρ 0 = 0) : Continuous (radialFun ρ : E → E) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    rw [ContinuousAt, radialFun_zero, tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_radialFun hρ hρ0]
    have : Tendsto (fun y : E => ρ ‖y‖) (𝓝 0) (𝓝 (ρ ‖(0 : E)‖)) :=
      (hρc.comp continuous_norm).continuousAt
    simpa [hρ0] using this
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    show ContinuousAt (fun y : E => (ρ ‖y‖ / ‖y‖) • y) x
    exact ((hρc.continuousAt.comp continuous_norm.continuousAt).div
      continuous_norm.continuousAt hn).smul continuousAt_id

theorem radialFun_radialFun {ρ τ : ℝ → ℝ} (hτ : ∀ t, 0 < t → 0 < τ t) (hτ0 : τ 0 = 0)
    (hρτ : ∀ t, ρ (τ t) = t) (x : E) : radialFun ρ (radialFun τ x) = x := by
  by_cases hx : x = 0
  · simp [hx, radialFun]
  · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hτn : 0 < τ ‖x‖ := hτ _ hn
    have hτnn : ∀ t, 0 ≤ t → 0 ≤ τ t := fun t ht => by
      rcases ht.eq_or_lt with h | h
      · rw [← h, hτ0]
      · exact (hτ t h).le
    have hnorm : ‖radialFun τ x‖ = τ ‖x‖ := norm_radialFun hτnn hτ0 x
    rw [radialFun, hnorm, hρτ, radialFun, smul_smul]
    have h1 : ‖x‖ ≠ 0 := hn.ne'
    have h2 : τ ‖x‖ ≠ 0 := hτn.ne'
    rw [show ‖x‖ / τ ‖x‖ * (τ ‖x‖ / ‖x‖) = 1 by field_simp, one_smul]

theorem orderIso_pos_of_map_zero (ρ : ℝ ≃o ℝ) (h : ρ 0 = 0) {t : ℝ} (ht : 0 < t) : 0 < ρ t := by
  simpa [h] using ρ.strictMono ht

theorem orderIso_nonneg_of_map_zero (ρ : ℝ ≃o ℝ) (h : ρ 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ρ t := by
  simpa [h] using ρ.monotone ht

theorem orderIso_symm_map_zero (ρ : ℝ ≃o ℝ) (h : ρ 0 = 0) : ρ.symm 0 = 0 :=
  ρ.symm_apply_eq.2 h.symm

/-- The radial homeomorphism of `E` induced by an order automorphism `ρ` of `ℝ` with
`ρ 0 = 0`: it rescales each vector so that its norm `t` becomes `ρ t`. -/
noncomputable def radialHomeomorph (ρ : ℝ ≃o ℝ) (hρ0 : ρ 0 = 0) : E ≃ₜ E where
  toFun := radialFun ρ
  invFun := radialFun ρ.symm
  left_inv := radialFun_radialFun (fun _ ht => orderIso_pos_of_map_zero ρ hρ0 ht) hρ0
    ρ.symm_apply_apply
  right_inv := radialFun_radialFun
    (fun _ ht => orderIso_pos_of_map_zero ρ.symm (orderIso_symm_map_zero ρ hρ0) ht)
    (orderIso_symm_map_zero ρ hρ0) ρ.apply_symm_apply
  continuous_toFun := continuous_radialFun ρ.continuous
    (fun _ ht => orderIso_nonneg_of_map_zero ρ hρ0 ht) hρ0
  continuous_invFun := continuous_radialFun ρ.symm.continuous
    (fun _ ht => orderIso_nonneg_of_map_zero ρ.symm (orderIso_symm_map_zero ρ hρ0) ht)
    (orderIso_symm_map_zero ρ hρ0)

theorem radialHomeomorph_apply (ρ : ℝ ≃o ℝ) (hρ0 : ρ 0 = 0) (x : E) :
    radialHomeomorph ρ hρ0 x = radialFun ρ x := rfl

end Radial

/-! ### The piecewise-linear squeeze -/

section PL

/-- The piecewise-linear function through `(0, 0)`, `(r, δ)`, `(1, 1)`, with slope `δ / r`
below `r` and slope `1` above `1`. For `0 < δ < r < 1` it is an order automorphism
of `ℝ`. -/
noncomputable def squeezeFun (δ r : ℝ) (t : ℝ) : ℝ :=
  max (δ / r * t) (min (δ + (1 - δ) / (1 - r) * (t - r)) t)

variable {δ r : ℝ}

theorem squeezeFun_strictMono (h0 : 0 < δ) (hδr : δ < r) (hr1 : r < 1) :
    StrictMono (squeezeFun δ r) := by
  intro a b hab
  have hr : 0 < r := h0.trans hδr
  have hs : 0 < (1 - δ) / (1 - r) := div_pos (by linarith) (by linarith)
  have h1 : δ / r * a < δ / r * b := mul_lt_mul_of_pos_left hab (div_pos h0 hr)
  have h2 : δ + (1 - δ) / (1 - r) * (a - r) < δ + (1 - δ) / (1 - r) * (b - r) := by
    have := mul_lt_mul_of_pos_left (sub_lt_sub_right hab r) hs
    linarith
  exact max_lt_max h1 (lt_min ((min_le_left _ _).trans_lt h2) ((min_le_right _ _).trans_lt hab))

theorem continuous_squeezeFun : Continuous (squeezeFun δ r) := by
  unfold squeezeFun
  fun_prop

theorem squeezeFun_surjective (h0 : 0 < δ) (hδr : δ < r) :
    Surjective (squeezeFun δ r) := by
  have hr : 0 < r := h0.trans hδr
  have hc : 0 < δ / r := div_pos h0 hr
  have hc1 : δ / r < 1 := (div_lt_one hr).2 hδr
  refine continuous_squeezeFun.surjective ?_ ?_
  · refine tendsto_atTop_mono (fun t => ?_) (tendsto_id.const_mul_atTop hc)
    exact le_max_left _ _
  · refine tendsto_atBot_mono' _ ?_ (tendsto_id.const_mul_atBot hc)
    filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
    refine max_le le_rfl ((min_le_right _ _).trans ?_)
    show t ≤ δ / r * t
    nlinarith

theorem squeezeFun_zero : squeezeFun δ r 0 = 0 := by
  unfold squeezeFun
  rw [mul_zero]
  exact max_eq_left (min_le_right _ _)

theorem squeezeFun_r (hr : 0 < r) (hδr : δ ≤ r) : squeezeFun δ r r = δ := by
  unfold squeezeFun
  rw [div_mul_cancel₀ δ hr.ne', sub_self, mul_zero, add_zero, min_eq_left hδr, max_self]

theorem squeezeFun_of_one_le (h0 : 0 < δ) (hδr : δ < r) (hr1 : r < 1) {t : ℝ} (ht : 1 ≤ t) :
    squeezeFun δ r t = t := by
  have hr : 0 < r := h0.trans hδr
  have hs1 : 1 ≤ (1 - δ) / (1 - r) := (one_le_div (by linarith)).2 (by linarith)
  have hsr : (1 - δ) / (1 - r) * (1 - r) = 1 - δ := div_mul_cancel₀ _ (by linarith)
  have hc1 : δ / r ≤ 1 := ((div_lt_one hr).2 hδr).le
  have hmin : min (δ + (1 - δ) / (1 - r) * (t - r)) t = t := by
    refine min_eq_right ?_
    have := mul_nonneg (sub_nonneg.2 hs1) (sub_nonneg.2 ht)
    nlinarith
  unfold squeezeFun
  rw [hmin]
  exact max_eq_right (by nlinarith)

/-- `squeezeFun δ r` as an order automorphism of `ℝ`. -/
noncomputable def squeezeOrderIso (h0 : 0 < δ) (hδr : δ < r) (hr1 : r < 1) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (squeezeFun δ r) (squeezeFun_strictMono h0 hδr hr1)
    (squeezeFun_surjective h0 hδr)

theorem squeezeOrderIso_apply (h0 : 0 < δ) (hδr : δ < r) (hr1 : r < 1) (t : ℝ) :
    squeezeOrderIso h0 hδr hr1 t = squeezeFun δ r t := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A homeomorphism of `E`, the identity outside the closed unit ball, that maps the
closed `r`-ball into the closed `δ`-ball. -/
noncomputable def squeezeHomeomorph (h0 : 0 < δ) (hδr : δ < r) (hr1 : r < 1) : E ≃ₜ E :=
  radialHomeomorph (squeezeOrderIso h0 hδr hr1) squeezeFun_zero

theorem squeezeHomeomorph_norm (h0 : 0 < δ) (hδr : δ < r) (hr1 : r < 1) (x : E) :
    ‖squeezeHomeomorph h0 hδr hr1 x‖ = squeezeFun δ r ‖x‖ :=
  norm_radialFun
    (fun _ ht => orderIso_nonneg_of_map_zero (squeezeOrderIso h0 hδr hr1) squeezeFun_zero ht)
    squeezeFun_zero x

theorem squeezeHomeomorph_eq_self (h0 : 0 < δ) (hδr : δ < r) (hr1 : r < 1) {x : E}
    (hx : 1 ≤ ‖x‖) : squeezeHomeomorph h0 hδr hr1 x = x :=
  radialFun_eq_self (squeezeFun_of_one_le h0 hδr hr1 hx)

theorem norm_squeezeHomeomorph_le_one (h0 : 0 < δ) (hδr : δ < r) (hr1 : r < 1) {x : E}
    (hx : ‖x‖ ≤ 1) : ‖squeezeHomeomorph h0 hδr hr1 x‖ ≤ 1 := by
  rw [squeezeHomeomorph_norm]
  calc squeezeFun δ r ‖x‖ ≤ squeezeFun δ r 1 := (squeezeFun_strictMono h0 hδr hr1).monotone hx
    _ = 1 := squeezeFun_of_one_le h0 hδr hr1 le_rfl

theorem norm_squeezeHomeomorph_le (h0 : 0 < δ) (hδr : δ < r) (hr1 : r < 1) {x : E}
    (hx : ‖x‖ ≤ r) : ‖squeezeHomeomorph h0 hδr hr1 x‖ ≤ δ := by
  rw [squeezeHomeomorph_norm]
  calc squeezeFun δ r ‖x‖ ≤ squeezeFun δ r r := (squeezeFun_strictMono h0 hδr hr1).monotone hx
    _ = δ := squeezeFun_r (h0.trans hδr) hδr.le

end PL

/-! ### Transplanting a compactly supported homeomorphism -/

section Transplant

variable {E M : Type*}

open Classical in
/-- `e ∘ σ ∘ e⁻¹` on the range of `e`, and the identity elsewhere. -/
noncomputable def transplantFun (e : E → M) (σ : E → E) (m : M) : M :=
  if h : ∃ x, e x = m then e (σ h.choose) else m

theorem transplantFun_apply {e : E → M} (he : Injective e) (σ : E → E) (x : E) :
    transplantFun e σ (e x) = e (σ x) := by
  have h : ∃ y, e y = e x := ⟨x, rfl⟩
  rw [transplantFun, dite_eq_left h, he h.choose_spec]

theorem transplantFun_of_notMem_range {e : E → M} (σ : E → E) {m : M} (hm : m ∉ range e) :
    transplantFun e σ m = m := by
  unfold transplantFun
  exact dite_eq_right hm

theorem transplantFun_eq_self {e : E → M} (he : Injective e) {σ : E → E} {K : Set E}
    (hσ : ∀ x ∉ K, σ x = x) {m : M} (hm : m ∉ e '' K) : transplantFun e σ m = m := by
  by_cases h : m ∈ range e
  · obtain ⟨x, rfl⟩ := h
    rw [transplantFun_apply he, hσ x (fun hx => hm (mem_image_of_mem e hx))]
  · exact transplantFun_of_notMem_range σ h

theorem transplantFun_transplantFun {e : E → M} (he : Injective e) {σ τ : E → E}
    (h : ∀ x, σ (τ x) = x) (m : M) : transplantFun e σ (transplantFun e τ m) = m := by
  by_cases hm : m ∈ range e
  · obtain ⟨x, rfl⟩ := hm
    rw [transplantFun_apply he, transplantFun_apply he, h]
  · rw [transplantFun_of_notMem_range τ hm, transplantFun_of_notMem_range σ hm]

theorem continuous_transplantFun [TopologicalSpace E] [TopologicalSpace M] [T2Space M] {e : E → M} (he : IsOpenEmbedding e)
    {σ : E → E} (hσc : Continuous σ) {K : Set E} (hK : IsCompact K)
    (hσ : ∀ x ∉ K, σ x = x) : Continuous (transplantFun e σ) := by
  rw [continuous_iff_continuousAt]
  intro m
  by_cases hm : m ∈ e '' K
  · obtain ⟨x, -, rfl⟩ := hm
    rw [← he.continuousAt_iff]
    have : transplantFun e σ ∘ e = e ∘ σ :=
      funext fun x => transplantFun_apply he.injective σ x
    rw [this]
    exact (he.continuous.comp hσc).continuousAt
  · have hopen : IsOpen (e '' K)ᶜ := (hK.image he.continuous).isClosed.isOpen_compl
    refine continuousAt_id.congr ?_
    filter_upwards [hopen.mem_nhds hm] with m' hm'
    exact (transplantFun_eq_self he.injective hσ hm').symm

/-- Transplant a homeomorphism `σ` of `E`, which is the identity outside the compact set
`K`, through the open embedding `e : E → M`: the result is `e ∘ σ ∘ e⁻¹` on the range
of `e` and the identity elsewhere. -/
noncomputable def transplant [TopologicalSpace E] [TopologicalSpace M] [T2Space M] {e : E → M} (he : IsOpenEmbedding e) (σ : E ≃ₜ E)
    {K : Set E} (hK : IsCompact K) (hσ : ∀ x ∉ K, σ x = x) : M ≃ₜ M where
  toFun := transplantFun e σ
  invFun := transplantFun e σ.symm
  left_inv := transplantFun_transplantFun he.injective σ.symm_apply_apply
  right_inv := transplantFun_transplantFun he.injective σ.apply_symm_apply
  continuous_toFun := continuous_transplantFun he σ.continuous hK hσ
  continuous_invFun := continuous_transplantFun he σ.symm.continuous hK
    fun x hx => σ.symm_apply_eq.2 (hσ x hx).symm

variable [TopologicalSpace E] [TopologicalSpace M] [T2Space M] {e : E → M} (he : IsOpenEmbedding e) (σ : E ≃ₜ E) {K : Set E}
  (hK : IsCompact K) (hσ : ∀ x ∉ K, σ x = x)

theorem transplant_apply (x : E) : transplant he σ hK hσ (e x) = e (σ x) :=
  transplantFun_apply he.injective σ x

theorem transplant_eq_self {m : M} (hm : m ∉ e '' K) : transplant he σ hK hσ m = m :=
  transplantFun_eq_self he.injective hσ hm

end Transplant

end DiscEmbedding

end
