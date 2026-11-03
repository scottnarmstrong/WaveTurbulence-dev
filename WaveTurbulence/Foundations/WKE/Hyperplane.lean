/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.Mom
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Slicing `ℝ^d` along a hyperplane

For `ℓ ≠ 0` in `Mom d` with unit vector `u = ℓ / |ℓ|`, the map `(t, w) ↦ t • u + w` from
`ℝ × ℓ^⊥` to `Mom d` is a measure-preserving equivalence (Lebesgue measure on `ℝ`, the
inner-product Haar measure on the hyperplane `ℓ^⊥ = (ℝ ∙ ℓ)ᗮ`). This is the measure-theoretic
content of the identity `∫ g(ℓ₃) δ(2⟨ℓ₁, ℓ₃⟩) dℓ₃ = (2|ℓ₁|)⁻¹ ∫_{ℓ₁^⊥} g` used to read the
collision operator (TARGET (C.5), L2512).

We also prove the uniform hyperplane bound `∫_{ℓ^⊥} (1 + |c + w|)^{-M} dw ≤ hypConst d M` for
`M > d - 1`, uniformly in `ℓ ≠ 0` and `c`.
-/

public section

open MeasureTheory Set Module
open scoped InnerProductSpace

namespace WaveTurbulence

variable {d : ℕ}

/-- The unit vector `ℓ / |ℓ|`. -/
@[expose] noncomputable def unitVec (ℓ : Mom d) : Mom d := ‖ℓ‖⁻¹ • ℓ

theorem norm_unitVec {ℓ : Mom d} (hℓ : ℓ ≠ 0) : ‖unitVec ℓ‖ = 1 := by
  simp [unitVec, norm_smul, hℓ]

theorem inner_unitVec_self (ℓ : Mom d) : ⟪ℓ, unitVec ℓ⟫_ℝ = ‖ℓ‖ := by
  by_cases hℓ : ℓ = 0
  · simp [hℓ, unitVec]
  · rw [unitVec, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp

theorem span_unitVec {ℓ : Mom d} (hℓ : ℓ ≠ 0) : (ℝ ∙ unitVec ℓ) = (ℝ ∙ ℓ) :=
  Submodule.span_singleton_smul_eq (by simpa using hℓ) ℓ

theorem inner_eq_zero_of_mem_perp {ℓ : Mom d} (w : ↥(ℝ ∙ ℓ)ᗮ) : ⟪ℓ, (w : Mom d)⟫_ℝ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2

theorem inner_unitVec_eq_zero_of_mem_perp {ℓ : Mom d} (w : ↥(ℝ ∙ ℓ)ᗮ) :
    ⟪unitVec ℓ, (w : Mom d)⟫_ℝ = 0 := by
  rw [unitVec, inner_smul_left, inner_eq_zero_of_mem_perp w]
  simp

/-- `ℝ ≃ₗᵢ ℝ ∙ ℓ`, `t ↦ t • ℓ / |ℓ|`. -/
@[expose] noncomputable def lineIsometry {ℓ : Mom d} (hℓ : ℓ ≠ 0) : ℝ ≃ₗᵢ[ℝ] ↥(ℝ ∙ ℓ) :=
  (LinearIsometryEquiv.toSpanUnitSingleton (unitVec ℓ) (norm_unitVec hℓ)).trans
    (LinearIsometryEquiv.ofEq _ _ (span_unitVec hℓ))

theorem coe_lineIsometry {ℓ : Mom d} (hℓ : ℓ ≠ 0) (t : ℝ) :
    ((lineIsometry hℓ t : ↥(ℝ ∙ ℓ)) : Mom d) = t • unitVec ℓ := rfl

/-- The slicing equivalence `ℝ × ℓ^⊥ ≃ᵐ Mom d`, `(t, w) ↦ t • ℓ / |ℓ| + w`. -/
@[expose] noncomputable def sliceEquiv {ℓ : Mom d} (hℓ : ℓ ≠ 0) : ℝ × ↥(ℝ ∙ ℓ)ᗮ ≃ᵐ Mom d :=
  ((lineIsometry hℓ).toMeasurableEquiv.prodCongr (MeasurableEquiv.refl _)).trans
    ((MeasurableEquiv.toLp 2 (↥(ℝ ∙ ℓ) × ↥(ℝ ∙ ℓ)ᗮ)).trans
      (ℝ ∙ ℓ).orthogonalDecomposition.symm.toMeasurableEquiv)

theorem sliceEquiv_apply {ℓ : Mom d} (hℓ : ℓ ≠ 0) (p : ℝ × ↥(ℝ ∙ ℓ)ᗮ) :
    sliceEquiv hℓ p = p.1 • unitVec ℓ + (p.2 : Mom d) := by
  rcases p with ⟨t, w⟩
  simp [sliceEquiv, MeasurableEquiv.prodCongr, coe_lineIsometry]

theorem measurePreserving_sliceEquiv {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    MeasurePreserving (sliceEquiv hℓ) := by
  have h1 : MeasurePreserving
      (Prod.map (lineIsometry hℓ) (id : ↥(ℝ ∙ ℓ)ᗮ → ↥(ℝ ∙ ℓ)ᗮ))
      (volume : Measure (ℝ × ↥(ℝ ∙ ℓ)ᗮ)) (volume : Measure (↥(ℝ ∙ ℓ) × ↥(ℝ ∙ ℓ)ᗮ)) :=
    (lineIsometry hℓ).measurePreserving.prod (MeasurePreserving.id _)
  have h2 := WithLp.volume_preserving_toLp ↥(ℝ ∙ ℓ) ↥(ℝ ∙ ℓ)ᗮ
  have h3 := ((ℝ ∙ ℓ).orthogonalDecomposition).symm.measurePreserving
  exact (h3.comp (h2.comp h1))

/-- Slicing formula: `∫_{ℝ^d} g = ∫_ℝ ∫_{ℓ^⊥} g(t • ℓ / |ℓ| + w) dw dt`. -/
theorem integral_eq_integral_slice {ℓ : Mom d} (hℓ : ℓ ≠ 0) {g : Mom d → ℝ}
    (hg : Integrable g) :
    ∫ x, g x = ∫ t : ℝ, ∫ w : ↥(ℝ ∙ ℓ)ᗮ, g (t • unitVec ℓ + w) := by
  have hmp := measurePreserving_sliceEquiv hℓ
  rw [← hmp.integral_comp' g]
  have hint : Integrable (g ∘ sliceEquiv hℓ) (volume : Measure (ℝ × ↥(ℝ ∙ ℓ)ᗮ)) :=
    hmp.integrable_comp_emb (sliceEquiv hℓ).measurableEmbedding |>.mpr hg
  rw [show (volume : Measure (ℝ × ↥(ℝ ∙ ℓ)ᗮ)) = volume.prod volume from rfl] at hint ⊢
  have h := integral_prod _ hint
  simp only [Function.comp_def, sliceEquiv_apply] at h
  simp only [sliceEquiv_apply]
  exact h

/-- Integrability of slices of an integrable function, for almost every `t`. -/
theorem integrable_slice_ae {ℓ : Mom d} (hℓ : ℓ ≠ 0) {g : Mom d → ℝ} (hg : Integrable g) :
    ∀ᵐ t : ℝ, Integrable (fun w : ↥(ℝ ∙ ℓ)ᗮ => g (t • unitVec ℓ + w)) := by
  have hmp := measurePreserving_sliceEquiv hℓ
  have hint : Integrable (g ∘ sliceEquiv hℓ) (volume : Measure (ℝ × ↥(ℝ ∙ ℓ)ᗮ)) :=
    hmp.integrable_comp_emb (sliceEquiv hℓ).measurableEmbedding |>.mpr hg
  rw [show (volume : Measure (ℝ × ↥(ℝ ∙ ℓ)ᗮ)) = volume.prod volume from rfl] at hint
  filter_upwards [hint.prod_right_ae] with t ht
  simpa [sliceEquiv_apply, Function.comp_def] using ht

/-! ### Orthogonal decomposition of a point relative to `ℓ` -/

/-- The component of `c` in the hyperplane `ℓ^⊥`. -/
@[expose] noncomputable def perpPart (ℓ : Mom d) (c : Mom d) : ↥(ℝ ∙ ℓ)ᗮ :=
  ⟨c - ⟪unitVec ℓ, c⟫_ℝ • unitVec ℓ, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, inner_smul_right,
      inner_unitVec_self]
    by_cases hℓ : ℓ = 0
    · simp [hℓ]
    · have key : ‖ℓ‖⁻¹ * ‖ℓ‖ = 1 := inv_mul_cancel₀ (norm_ne_zero_iff.mpr hℓ)
      rw [unitVec, real_inner_smul_left]
      linear_combination (-⟪ℓ, c⟫_ℝ) * key⟩

theorem coe_perpPart (ℓ c : Mom d) :
    ((perpPart ℓ c : ↥(ℝ ∙ ℓ)ᗮ) : Mom d) = c - ⟪unitVec ℓ, c⟫_ℝ • unitVec ℓ := rfl

theorem eq_smul_add_perpPart (ℓ c : Mom d) :
    c = ⟪unitVec ℓ, c⟫_ℝ • unitVec ℓ + (perpPart ℓ c : Mom d) := by
  rw [coe_perpPart]; abel

/-- Pythagoras for the slicing coordinates. -/
theorem norm_sq_smul_unitVec_add {ℓ : Mom d} (hℓ : ℓ ≠ 0) (a : ℝ) (w : ↥(ℝ ∙ ℓ)ᗮ) :
    ‖a • unitVec ℓ + (w : Mom d)‖ ^ 2 = a ^ 2 + ‖(w : Mom d)‖ ^ 2 := by
  rw [norm_add_sq_real, inner_smul_left, inner_unitVec_eq_zero_of_mem_perp w, norm_smul,
    norm_unitVec hℓ]
  simp [sq_abs]

theorem norm_perp_le_norm_smul_unitVec_add {ℓ : Mom d} (hℓ : ℓ ≠ 0) (a : ℝ)
    (w : ↥(ℝ ∙ ℓ)ᗮ) : ‖(w : Mom d)‖ ≤ ‖a • unitVec ℓ + (w : Mom d)‖ := by
  have h := norm_sq_smul_unitVec_add hℓ a w
  nlinarith [norm_nonneg (w : Mom d), norm_nonneg (a • unitVec ℓ + (w : Mom d)), sq_nonneg a]

/-- For `w ∈ ℓ^⊥` and any `c`, `|perpPart c + w| ≤ |c + t • u + w|`. -/
theorem norm_perpPart_add_le {ℓ : Mom d} (hℓ : ℓ ≠ 0) (c : Mom d) (t : ℝ) (w : ↥(ℝ ∙ ℓ)ᗮ) :
    ‖((perpPart ℓ c + w : ↥(ℝ ∙ ℓ)ᗮ) : Mom d)‖ ≤ ‖c + t • unitVec ℓ + (w : Mom d)‖ := by
  have : c + t • unitVec ℓ + (w : Mom d) =
      (⟪unitVec ℓ, c⟫_ℝ + t) • unitVec ℓ + ((perpPart ℓ c + w : ↥(ℝ ∙ ℓ)ᗮ) : Mom d) := by
    rw [Submodule.coe_add, coe_perpPart, add_smul]; abel
  rw [this]
  exact norm_perp_le_norm_smul_unitVec_add hℓ _ _

/-! ### The uniform hyperplane bound -/

theorem finrank_perp {ℓ : Mom d} (hℓ : ℓ ≠ 0) : finrank ℝ ↥(ℝ ∙ ℓ)ᗮ = d - 1 := by
  have h := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ ℓ)
  rw [finrank_span_singleton hℓ, finrank_euclideanSpace_fin] at h
  omega

/-- The integral `∫_{ℝ^{d-1}} (1 + |x|)^{-M} dx`, the uniform bound for hyperplane integrals. -/
@[expose] noncomputable def hypConst (d : ℕ) (M : ℝ) : ℝ :=
  ∫ x : EuclideanSpace ℝ (Fin (d - 1)), (1 + ‖x‖) ^ (-M)

theorem hypConst_nonneg (d : ℕ) (M : ℝ) : 0 ≤ hypConst d M :=
  integral_nonneg fun _ => by positivity

/-- A linear isometry from the hyperplane `ℓ^⊥` onto `ℝ^{d-1}`. -/
noncomputable def perpIsometry {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    ↥(ℝ ∙ ℓ)ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d - 1)) :=
  ((stdOrthonormalBasis ℝ ↥(ℝ ∙ ℓ)ᗮ).reindex (finCongr (finrank_perp hℓ))).repr

theorem integral_perp_radial {ℓ : Mom d} (hℓ : ℓ ≠ 0) (f : ℝ → ℝ) :
    ∫ w : ↥(ℝ ∙ ℓ)ᗮ, f ‖(w : Mom d)‖ = ∫ x : EuclideanSpace ℝ (Fin (d - 1)), f ‖x‖ := by
  have hmp := (perpIsometry hℓ).measurePreserving
  rw [← hmp.integral_comp' (f := (perpIsometry hℓ).toMeasurableEquiv)]
  congr 1
  ext w
  simp only [LinearIsometryEquiv.coe_toMeasurableEquiv, LinearIsometryEquiv.norm_map]
  rfl

theorem integrable_one_add_norm_perp {ℓ : Mom d} (hℓ : ℓ ≠ 0) {M : ℝ} (hM : (d : ℝ) - 1 < M)
    (c : ↥(ℝ ∙ ℓ)ᗮ) :
    Integrable (fun w : ↥(ℝ ∙ ℓ)ᗮ => (1 + ‖((c + w : ↥(ℝ ∙ ℓ)ᗮ) : Mom d)‖) ^ (-M)) := by
  have hfr : (finrank ℝ ↥(ℝ ∙ ℓ)ᗮ : ℝ) < M := by
    rw [finrank_perp hℓ]
    have : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · subst h; exact absurd (Subsingleton.elim ℓ 0) hℓ
      · exact h
    push_cast [Nat.cast_sub this]
    linarith
  have h := (integrable_one_add_norm (E := ↥(ℝ ∙ ℓ)ᗮ) (μ := volume) hfr).comp_add_left c
  simpa [Function.comp_def] using h

theorem integral_one_add_norm_perp {ℓ : Mom d} (hℓ : ℓ ≠ 0) (M : ℝ) (c : ↥(ℝ ∙ ℓ)ᗮ) :
    ∫ w : ↥(ℝ ∙ ℓ)ᗮ, (1 + ‖((c + w : ↥(ℝ ∙ ℓ)ᗮ) : Mom d)‖) ^ (-M) = hypConst d M := by
  have h : ∫ w : ↥(ℝ ∙ ℓ)ᗮ, (1 + ‖((c + w : ↥(ℝ ∙ ℓ)ᗮ) : Mom d)‖) ^ (-M) =
      ∫ w : ↥(ℝ ∙ ℓ)ᗮ, (1 + ‖(w : Mom d)‖) ^ (-M) :=
    integral_add_left_eq_self (fun w : ↥(ℝ ∙ ℓ)ᗮ => (1 + ‖(w : Mom d)‖) ^ (-M)) c
  rw [h, integral_perp_radial hℓ (fun r => (1 + r) ^ (-M))]
  rfl

/-- **Uniform hyperplane bound.** For `M > d - 1`, `ℓ ≠ 0`, `c ∈ ℝ^d` and `t ∈ ℝ`,
`∫_{ℓ^⊥} (1 + |c + t • u + w|)^{-M} dw ≤ hypConst d M`; the integrand is integrable and is
dominated by the `t`-independent integrable function `(1 + |perpPart c + w|)^{-M}`. -/
theorem one_add_norm_slice_le {ℓ : Mom d} (hℓ : ℓ ≠ 0) {M : ℝ} (hM : 0 ≤ M) (c : Mom d)
    (t : ℝ) (w : ↥(ℝ ∙ ℓ)ᗮ) :
    (1 + ‖c + t • unitVec ℓ + (w : Mom d)‖) ^ (-M) ≤
      (1 + ‖((perpPart ℓ c + w : ↥(ℝ ∙ ℓ)ᗮ) : Mom d)‖) ^ (-M) := by
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
  linarith [norm_perpPart_add_le hℓ c t w]

theorem integrable_one_add_norm_slice {ℓ : Mom d} (hℓ : ℓ ≠ 0) {M : ℝ} (hM : (d : ℝ) - 1 < M)
    (hM0 : 0 ≤ M) (c : Mom d) (t : ℝ) :
    Integrable (fun w : ↥(ℝ ∙ ℓ)ᗮ => (1 + ‖c + t • unitVec ℓ + (w : Mom d)‖) ^ (-M)) := by
  refine (integrable_one_add_norm_perp hℓ hM (perpPart ℓ c)).mono' ?_ ?_
  · exact Continuous.aestronglyMeasurable
      ((by fun_prop : Continuous fun w : ↥(ℝ ∙ ℓ)ᗮ => 1 + ‖c + t • unitVec ℓ + (w : Mom d)‖).rpow_const
        fun _ => Or.inl (ne_of_gt (by positivity)))
  · refine Filter.Eventually.of_forall fun w => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact one_add_norm_slice_le hℓ hM0 c t w

theorem integral_one_add_norm_slice_le {ℓ : Mom d} (hℓ : ℓ ≠ 0) {M : ℝ}
    (hM : (d : ℝ) - 1 < M) (hM0 : 0 ≤ M) (c : Mom d) (t : ℝ) :
    ∫ w : ↥(ℝ ∙ ℓ)ᗮ, (1 + ‖c + t • unitVec ℓ + (w : Mom d)‖) ^ (-M) ≤ hypConst d M := by
  rw [← integral_one_add_norm_perp hℓ M (perpPart ℓ c)]
  exact integral_mono (integrable_one_add_norm_slice hℓ hM hM0 c t)
    (integrable_one_add_norm_perp hℓ hM _) (one_add_norm_slice_le hℓ hM0 c t)

end WaveTurbulence
