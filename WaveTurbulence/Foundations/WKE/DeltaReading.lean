/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.Hyperplane
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Reading `δ(2⟨ℓ₁, ℓ₃⟩)` on a hyperplane

For a kernel `F(ℓ₁, ℓ₃)` on `ℝ^d × ℝ^d` we define

* `deltaInt F = ∫ (2|ℓ₁|)⁻¹ ∫_{ℓ₁^⊥} F(ℓ₁, w) dw dℓ₁` — the reading of
  `∫∫ F(ℓ₁, ℓ₃) δ(2⟨ℓ₁, ℓ₃⟩) dℓ₁ dℓ₃` used by `collisionOp`;
* `molInner ψ ε F ℓ₁ = ∫ F(ℓ₁, ℓ₃) ψ_ε(2⟨ℓ₁, ℓ₃⟩) dℓ₃` with `ψ_ε = ε⁻¹ ψ(·/ε)`.

Under a decay hypothesis on `F` (`DeltaKernel`), every integrand in `deltaInt F` is integrable
(no Bochner junk value is used) and `∫ molInner ψ ε F → deltaInt F` as `ε → 0⁺` for every
continuous compactly supported `ψ` with `∫ ψ = 1` (the convention of GIT20, Kin8.tex L981).
-/

public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace WaveTurbulence

variable {d : ℕ}

/-- `∫∫ F(ℓ₁, ℓ₃) δ(2⟨ℓ₁, ℓ₃⟩) dℓ₁ dℓ₃`, read as `∫ (2|ℓ₁|)⁻¹ ∫_{ℓ₁^⊥} F(ℓ₁, w) dw dℓ₁`. -/
@[expose] noncomputable def deltaInt (F : Mom d → Mom d → ℝ) : ℝ :=
  ∫ ℓ₁ : Mom d, (2 * ‖ℓ₁‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ₁)ᗮ, F ℓ₁ w

/-- The rescaled mollifier `ψ_ε(x) = ε⁻¹ ψ(x / ε)`. -/
@[expose] noncomputable def mollifier (ψ : ℝ → ℝ) (ε x : ℝ) : ℝ := ε⁻¹ * ψ (x / ε)

/-- The inner mollified integral `∫ F(ℓ₁, ℓ₃) ψ_ε(2⟨ℓ₁, ℓ₃⟩) dℓ₃`. -/
@[expose] noncomputable def molInner (ψ : ℝ → ℝ) (ε : ℝ) (F : Mom d → Mom d → ℝ) (ℓ₁ : Mom d) :
    ℝ :=
  ∫ ℓ₃ : Mom d, F ℓ₁ ℓ₃ * mollifier ψ ε (2 * ⟪ℓ₁, ℓ₃⟫_ℝ)

/-- The slice integral `t ↦ ∫_{ℓ^⊥} F(ℓ, t • ℓ/|ℓ| + w) dw`. -/
@[expose] noncomputable def sliceInt (F : Mom d → Mom d → ℝ) (ℓ : Mom d) (t : ℝ) : ℝ :=
  ∫ w : ↥(ℝ ∙ ℓ)ᗮ, F ℓ (t • unitVec ℓ + w)

/-- Decay hypotheses on a kernel `F(ℓ₁, x)`: joint continuity and a bound
`|F(ℓ₁, x)| ≤ A(ℓ₁) (1 + |b(ℓ₁) + x|)^{-M}` with `M > d` and `|ℓ₁|⁻¹ A(ℓ₁)` integrable. -/
structure DeltaKernel (F : Mom d → Mom d → ℝ) (A : Mom d → ℝ) (b : Mom d → Mom d) (M : ℝ) :
    Prop where
  cont : Continuous (Function.uncurry F)
  bound : ∀ ℓ x, |F ℓ x| ≤ A ℓ * (1 + ‖b ℓ + x‖) ^ (-M)
  dim : (d : ℝ) < M
  integrable : Integrable (fun ℓ : Mom d => ‖ℓ‖⁻¹ * A ℓ)

/-- Standard mollifier hypotheses. -/
structure IsMollifier (ψ : ℝ → ℝ) : Prop where
  cont : Continuous ψ
  compact : HasCompactSupport ψ
  integral_eq_one : ∫ x, ψ x = 1

namespace IsMollifier

variable {ψ : ℝ → ℝ}

theorem integrable (hψ : IsMollifier ψ) : Integrable ψ :=
  hψ.cont.integrable_of_hasCompactSupport hψ.compact

theorem exists_bound (hψ : IsMollifier ψ) : ∃ C, ∀ x, |ψ x| ≤ C := by
  obtain ⟨C, hC⟩ := hψ.cont.bounded_above_of_compact_support hψ.compact
  exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC x⟩

theorem continuous_mollifier (hψ : IsMollifier ψ) (ε : ℝ) : Continuous (mollifier ψ ε) := by
  unfold mollifier
  exact continuous_const.mul (hψ.cont.comp (continuous_id.div_const ε))

theorem exists_bound_mollifier (hψ : IsMollifier ψ) (ε : ℝ) :
    ∃ C, ∀ x, |mollifier ψ ε x| ≤ C := by
  obtain ⟨C, hC⟩ := hψ.exists_bound
  refine ⟨|ε⁻¹| * C, fun x => ?_⟩
  rw [mollifier, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)

end IsMollifier

/-- A standard mollifier exists (a normalized smooth bump). -/
theorem exists_isMollifier : ∃ ψ : ℝ → ℝ, IsMollifier ψ := by
  let f : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  exact ⟨f.normed volume, f.continuous_normed, f.hasCompactSupport_normed, f.integral_normed⟩

/-! ### One-dimensional facts -/

section OneDim

variable {ψ : ℝ → ℝ}

/-- Change of variables: `∫ ψ_ε(a t) h(t) dt = a⁻¹ ∫ ψ(y) h(ε y / a) dy` for `ε, a > 0`. -/
theorem integral_mollifier_mul_eq {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) (h : ℝ → ℝ) :
    ∫ t, mollifier ψ ε (a * t) * h t = a⁻¹ * ∫ y, ψ y * h (ε * y / a) := by
  have hc : 0 < a / ε := div_pos ha hε
  have key := Measure.integral_comp_mul_left (fun y => ε⁻¹ * ψ y * h (y / (a / ε))) (a / ε)
  have e1 : (fun t => mollifier ψ ε (a * t) * h t) =
      fun t => ε⁻¹ * ψ (a / ε * t) * h (a / ε * t / (a / ε)) := by
    funext t
    rw [mollifier, mul_div_cancel_left₀ _ hc.ne', div_mul_eq_mul_div]
  rw [e1, key, smul_eq_mul, ← integral_const_mul, ← integral_const_mul]
  congr 1
  funext y
  rw [abs_of_pos (inv_pos.mpr hc), div_div_eq_mul_div]
  field_simp

theorem integral_abs_mollifier_eq {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    ∫ t, |mollifier ψ ε (a * t)| = a⁻¹ * ∫ y, |ψ y| := by
  have h := integral_mollifier_mul_eq (ψ := fun y => |ψ y|) hε ha (fun _ => 1)
  simp only [mul_one] at h
  rw [← h]
  congr 1
  funext t
  simp [mollifier, abs_mul, abs_of_pos hε]

theorem integrable_mollifier_comp_mul (hψ : IsMollifier ψ) {ε a : ℝ} (hε : 0 < ε)
    (ha : 0 < a) : Integrable (fun t => mollifier ψ ε (a * t)) := by
  have h : Integrable (fun t => ψ (a / ε * t)) :=
    hψ.integrable.comp_mul_left' (div_pos ha hε).ne'
  refine (h.const_mul ε⁻¹).congr (Eventually.of_forall fun t => ?_)
  simp only [mollifier]
  congr 2
  field_simp

/-- `|∫ ψ_ε(a t) h(t) dt| ≤ a⁻¹ (∫|ψ|) B` when `|h| ≤ B`. -/
theorem abs_integral_mollifier_mul_le (hψ : IsMollifier ψ) {ε a : ℝ} (hε : 0 < ε)
    (ha : 0 < a) {h : ℝ → ℝ} {B : ℝ} (hB : ∀ t, |h t| ≤ B) :
    |∫ t, mollifier ψ ε (a * t) * h t| ≤ a⁻¹ * (∫ y, |ψ y|) * B := by
  have hint := (integrable_mollifier_comp_mul hψ hε ha).abs.mul_const B
  calc |∫ t, mollifier ψ ε (a * t) * h t|
      ≤ ∫ t, |mollifier ψ ε (a * t)| * B := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun t => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hB t) (abs_nonneg _)
    _ = a⁻¹ * (∫ y, |ψ y|) * B := by
        rw [integral_mul_const, integral_abs_mollifier_eq hε ha]

/-- **One-dimensional delta reading.** For a mollifier `ψ`, `a > 0` and a bounded continuous
`h`, `∫ ψ_ε(a t) h(t) dt → a⁻¹ h(0)` as `ε → 0⁺`. -/
theorem tendsto_integral_mollifier_mul (hψ : IsMollifier ψ) {a : ℝ} (ha : 0 < a)
    {h : ℝ → ℝ} (hc : Continuous h) {B : ℝ} (hB : ∀ t, |h t| ≤ B) :
    Tendsto (fun ε => ∫ t, mollifier ψ ε (a * t) * h t) (𝓝[>] 0) (𝓝 (a⁻¹ * h 0)) := by
  have hlim : Tendsto (fun ε => ∫ y, ψ y * h (ε * y / a)) (𝓝[>] 0) (𝓝 (∫ y, ψ y * h 0)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y => |ψ y| * B) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun ε =>
        (hψ.cont.mul (hc.comp ((continuous_const.mul continuous_id).div_const a))).aestronglyMeasurable
    · refine Eventually.of_forall fun ε => Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _)
    · exact hψ.integrable.abs.mul_const B
    · refine Eventually.of_forall fun y => ?_
      refine tendsto_const_nhds.mul ?_
      have : Tendsto (fun ε : ℝ => ε * y / a) (𝓝[>] 0) (𝓝 (0 * y / a)) :=
        ((tendsto_id.mul_const y).div_const a).mono_left nhdsWithin_le_nhds
      rw [zero_mul, zero_div] at this
      exact (hc.tendsto 0).comp this
  have hval : ∫ y, ψ y * h 0 = h 0 := by rw [integral_mul_const, hψ.integral_eq_one, one_mul]
  rw [hval] at hlim
  refine (hlim.const_mul a⁻¹).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_mollifier_mul_eq hε ha h).symm

end OneDim

/-! ### Slices of a decaying kernel -/

namespace DeltaKernel

variable {F : Mom d → Mom d → ℝ} {A : Mom d → ℝ} {b : Mom d → Mom d} {M : ℝ}

theorem M_nonneg (hK : DeltaKernel F A b M) : 0 ≤ M :=
  le_trans (Nat.cast_nonneg d) hK.dim.le

theorem A_nonneg (hK : DeltaKernel F A b M) (ℓ : Mom d) : 0 ≤ A ℓ := by
  have h := (abs_nonneg _).trans (hK.bound ℓ 0)
  exact (mul_nonneg_iff_of_pos_right (by positivity)).mp h

theorem continuous_right (hK : DeltaKernel F A b M) (ℓ : Mom d) : Continuous (F ℓ) :=
  hK.cont.comp (Continuous.prodMk continuous_const continuous_id)

theorem integrable_right (hK : DeltaKernel F A b M) (ℓ : Mom d) : Integrable (F ℓ) := by
  have hfr : (Module.finrank ℝ (Mom d) : ℝ) < M := by
    rw [finrank_euclideanSpace_fin]; exact hK.dim
  have hI := ((integrable_one_add_norm (E := Mom d) (μ := volume) hfr).comp_add_left
    (b ℓ)).const_mul (A ℓ)
  refine hI.mono' (hK.continuous_right ℓ).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact hK.bound ℓ x

theorem dim_sub_one_lt (hK : DeltaKernel F A b M) : (d : ℝ) - 1 < M := by
  linarith [hK.dim]

theorem slice_bound (hK : DeltaKernel F A b M) {ℓ : Mom d} (hℓ : ℓ ≠ 0) (t : ℝ)
    (w : ↥(ℝ ∙ ℓ)ᗮ) :
    |F ℓ (t • unitVec ℓ + w)| ≤
      A ℓ * (1 + ‖((perpPart ℓ (b ℓ) + w : ↥(ℝ ∙ ℓ)ᗮ) : Mom d)‖) ^ (-M) := by
  refine (hK.bound ℓ _).trans (mul_le_mul_of_nonneg_left ?_ (hK.A_nonneg ℓ))
  rw [← add_assoc]
  exact one_add_norm_slice_le hℓ hK.M_nonneg (b ℓ) t w

theorem integrable_slice_dom (hK : DeltaKernel F A b M) {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    Integrable (fun w : ↥(ℝ ∙ ℓ)ᗮ =>
      A ℓ * (1 + ‖((perpPart ℓ (b ℓ) + w : ↥(ℝ ∙ ℓ)ᗮ) : Mom d)‖) ^ (-M)) :=
  (integrable_one_add_norm_perp hℓ hK.dim_sub_one_lt _).const_mul _

theorem continuous_slice (hK : DeltaKernel F A b M) (ℓ : Mom d) (t : ℝ) :
    Continuous (fun w : ↥(ℝ ∙ ℓ)ᗮ => F ℓ (t • unitVec ℓ + w)) :=
  (hK.continuous_right ℓ).comp (continuous_const.add continuous_subtype_val)

theorem integrable_slice (hK : DeltaKernel F A b M) {ℓ : Mom d} (hℓ : ℓ ≠ 0) (t : ℝ) :
    Integrable (fun w : ↥(ℝ ∙ ℓ)ᗮ => F ℓ (t • unitVec ℓ + w)) :=
  (hK.integrable_slice_dom hℓ).mono' (hK.continuous_slice ℓ t).aestronglyMeasurable
    (Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hK.slice_bound hℓ t w)

/-- The inner hyperplane integrand of `deltaInt F` is integrable. -/
theorem integrable_perp (hK : DeltaKernel F A b M) {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    Integrable (fun w : ↥(ℝ ∙ ℓ)ᗮ => F ℓ w) := by
  simpa using hK.integrable_slice hℓ 0

theorem abs_sliceInt_le (hK : DeltaKernel F A b M) {ℓ : Mom d} (hℓ : ℓ ≠ 0) (t : ℝ) :
    |sliceInt F ℓ t| ≤ A ℓ * hypConst d M := by
  rw [← Real.norm_eq_abs, sliceInt]
  refine (norm_integral_le_of_norm_le (hK.integrable_slice_dom hℓ)
    (Eventually.of_forall fun w => ?_)).trans_eq ?_
  · rw [Real.norm_eq_abs]; exact hK.slice_bound hℓ t w
  · rw [integral_const_mul, integral_one_add_norm_perp hℓ M]

theorem continuous_sliceInt (hK : DeltaKernel F A b M) {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    Continuous (sliceInt F ℓ) := by
  refine continuous_of_dominated (fun t => (hK.continuous_slice ℓ t).aestronglyMeasurable)
    (fun t => Eventually.of_forall fun w => ?_) (hK.integrable_slice_dom hℓ)
    (Eventually.of_forall fun w => ?_)
  · rw [Real.norm_eq_abs]; exact hK.slice_bound hℓ t w
  · exact (hK.continuous_right ℓ).comp ((continuous_id.smul continuous_const).add continuous_const)

/-- The slice representation of the inner mollified integral. -/
theorem molInner_eq (hK : DeltaKernel F A b M) {ψ : ℝ → ℝ} (hψ : IsMollifier ψ) (ε : ℝ)
    {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    molInner ψ ε F ℓ = ∫ t, mollifier ψ ε ((2 * ‖ℓ‖) * t) * sliceInt F ℓ t := by
  obtain ⟨C, hC⟩ := hψ.exists_bound_mollifier ε
  have hint : Integrable (fun x => F ℓ x * mollifier ψ ε (2 * ⟪ℓ, x⟫_ℝ)) := by
    refine (hK.integrable_right ℓ).mul_bdd (c := C) ?_ (Eventually.of_forall fun x => ?_)
    · exact ((hψ.continuous_mollifier ε).comp
        (continuous_const.mul (continuous_const.inner continuous_id))).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hC _
  rw [molInner, integral_eq_integral_slice hℓ hint]
  congr 1
  funext t
  have hin : ∀ w : ↥(ℝ ∙ ℓ)ᗮ, ⟪ℓ, t • unitVec ℓ + (w : Mom d)⟫_ℝ = t * ‖ℓ‖ := by
    intro w
    rw [inner_add_right, inner_smul_right, inner_unitVec_self, inner_eq_zero_of_mem_perp w,
      add_zero]
  simp_rw [hin]
  rw [sliceInt, integral_mul_const, mul_comm]
  ring_nf

theorem stronglyMeasurable_molInner (hK : DeltaKernel F A b M) {ψ : ℝ → ℝ}
    (hψ : IsMollifier ψ) (ε : ℝ) : StronglyMeasurable (molInner ψ ε F) := by
  refine StronglyMeasurable.integral_prod_right (f := fun ℓ₁ ℓ₃ =>
    F ℓ₁ ℓ₃ * mollifier ψ ε (2 * ⟪ℓ₁, ℓ₃⟫_ℝ)) ?_
  refine Continuous.stronglyMeasurable ?_
  exact hK.cont.mul ((hψ.continuous_mollifier ε).comp
    (continuous_const.mul (continuous_fst.inner continuous_snd)))

theorem abs_molInner_le (hK : DeltaKernel F A b M) {ψ : ℝ → ℝ} (hψ : IsMollifier ψ)
    {ε : ℝ} (hε : 0 < ε) {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    |molInner ψ ε F ℓ| ≤ (2 * ‖ℓ‖)⁻¹ * (∫ y, |ψ y|) * (A ℓ * hypConst d M) := by
  rw [hK.molInner_eq hψ ε hℓ]
  exact abs_integral_mollifier_mul_le hψ hε (by positivity) (hK.abs_sliceInt_le hℓ)

theorem tendsto_molInner (hK : DeltaKernel F A b M) {ψ : ℝ → ℝ} (hψ : IsMollifier ψ)
    {ℓ : Mom d} (hℓ : ℓ ≠ 0) :
    Tendsto (fun ε => molInner ψ ε F ℓ) (𝓝[>] 0)
      (𝓝 ((2 * ‖ℓ‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ)ᗮ, F ℓ w)) := by
  have h := tendsto_integral_mollifier_mul hψ (by positivity : 0 < 2 * ‖ℓ‖)
    (hK.continuous_sliceInt hℓ) (hK.abs_sliceInt_le hℓ)
  have h0 : sliceInt F ℓ 0 = ∫ w : ↥(ℝ ∙ ℓ)ᗮ, F ℓ w := by simp [sliceInt]
  rw [h0] at h
  refine h.congr' (Eventually.of_forall fun ε => ?_)
  exact (hK.molInner_eq hψ ε hℓ).symm

theorem ae_ne_zero (hd : 0 < d) : ∀ᵐ ℓ : Mom d, ℓ ≠ 0 := by
  have : Nontrivial (Mom d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hd)
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : Mom d))] with ℓ hℓ
  simpa using hℓ

/-- The outer integrand of `deltaInt F` is integrable. -/
theorem integrable_outer (hK : DeltaKernel F A b M) (hd : 0 < d) :
    Integrable (fun ℓ₁ : Mom d => (2 * ‖ℓ₁‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ₁)ᗮ, F ℓ₁ w) := by
  obtain ⟨ψ, hψ⟩ := exists_isMollifier
  have hmeas : AEStronglyMeasurable
      (fun ℓ₁ : Mom d => (2 * ‖ℓ₁‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ₁)ᗮ, F ℓ₁ w) :=
    aestronglyMeasurable_of_tendsto_ae (𝓝[>] (0 : ℝ))
      (fun ε => (hK.stronglyMeasurable_molInner hψ ε).aestronglyMeasurable)
      ((ae_ne_zero hd).mono fun ℓ hℓ => hK.tendsto_molInner hψ hℓ)
  refine ((hK.integrable.const_mul (2⁻¹ * hypConst d M))).mono' hmeas ?_
  filter_upwards [ae_ne_zero hd] with ℓ hℓ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
  have h2 : |∫ w : ↥(ℝ ∙ ℓ)ᗮ, F ℓ w| ≤ A ℓ * hypConst d M := by
    simpa [sliceInt] using hK.abs_sliceInt_le hℓ 0
  calc (2 * ‖ℓ‖)⁻¹ * |∫ w : ↥(ℝ ∙ ℓ)ᗮ, F ℓ w| ≤ (2 * ‖ℓ‖)⁻¹ * (A ℓ * hypConst d M) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2⁻¹ * hypConst d M * (‖ℓ‖⁻¹ * A ℓ) := by rw [mul_inv]; ring

/-- **Delta reading (abstract form).** For a decaying kernel and a mollifier `ψ`,
`∫∫ F(ℓ₁, ℓ₃) ψ_ε(2⟨ℓ₁, ℓ₃⟩) dℓ₃ dℓ₁ → deltaInt F` as `ε → 0⁺`. -/
theorem tendsto_integral_molInner (hK : DeltaKernel F A b M) (hd : 0 < d) {ψ : ℝ → ℝ}
    (hψ : IsMollifier ψ) :
    Tendsto (fun ε => ∫ ℓ₁, molInner ψ ε F ℓ₁) (𝓝[>] 0) (𝓝 (deltaInt F)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ℓ => 2⁻¹ * (∫ y, |ψ y|) * hypConst d M * (‖ℓ‖⁻¹ * A ℓ)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun ε => (hK.stronglyMeasurable_molInner hψ ε).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [ae_ne_zero hd] with ℓ hℓ
    rw [Real.norm_eq_abs]
    refine (hK.abs_molInner_le hψ hε hℓ).trans_eq ?_
    rw [mul_inv]; ring
  · exact hK.integrable.const_mul _
  · filter_upwards [ae_ne_zero hd] with ℓ hℓ
    exact hK.tendsto_molInner hψ hℓ

end DeltaKernel

end WaveTurbulence
