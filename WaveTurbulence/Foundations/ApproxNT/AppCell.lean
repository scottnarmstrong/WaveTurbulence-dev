/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.AppSplit

/-!
# The `J^c` factor of one cell: `Ψ₁(μ⟨x,y⟩) → (∫Ψ₁) δ(⟨x,y⟩)` (packet NT6)

For the `J^c` variables, `B = ∫ Ψ̂₁(b) ∏ᵢ cellInt_i(μ bᵢ) db` is compared with
`Δ = Ψ̂₁(0) ∏ᵢ ∫ cellInt_i(μt) dt = (∫Ψ₁) ∏ᵢ μ⁻¹ δᵢ` through the Hölder bound for `Ψ̂₁`:
`|B - Δ| ≤ 4π H m μ^{-θ} (μ⁻¹ C)^m`, `m = |J^c|`, `H = ‖max ⟨Ωᵢ⟩^θ Ψ₁‖_{L¹}`.
This is the step of DH21 Prop 6.1 (L1652–L1657) replacing `μΨ(μΩ)` by `(∫Ψ)δ(Ω)`, done for all
`J^c` variables at once.
-/

public section

noncomputable section

open MeasureTheory Finset WithLp
open scoped ContDiff FourierTransform ENNReal

namespace WaveTurbulence.ApproxNT

variable {d : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]

theorem prod_ite_mul_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (l : ι) (a t : ι → ℝ≥0∞) :
    ∏ i, (if i = l then a i * t i else t i) = a l * ∏ i, t i := by
  rw [← mul_prod_erase univ _ (mem_univ l), ← mul_prod_erase univ t (mem_univ l)]
  simp only [ite_true]
  rw [mul_assoc]
  congr 2
  exact prod_congr rfl fun i hi => by simp [ne_of_mem_erase hi]

/-- The constant of the one-dimensional cell integrals. -/
@[expose] def cellCa (d : ℕ) : ℝ := max (cellK0 d * NTSP.sInt d) (max (cellK0 d * NTSP.sInt (d - 1)) 1)

theorem one_le_cellCa (d : ℕ) : 1 ≤ cellCa d := le_max_of_le_right (le_max_right _ _)

theorem integrable_cellInt_scale (hd : 2 ≤ d) {μ : ℝ} (hμ : 0 < μ) (p q ξ η : Mom d) :
    Integrable (fun t => cellInt p q ξ η (μ * t)) :=
  (integrable_cellInt hd p q ξ η).comp_mul_left' hμ.ne'

omit [DecidableEq κ] in
theorem norm_B_le (hd : 3 ≤ d) {μ : ℝ} (hμ : 0 < μ) {f : EuclideanSpace ℝ κ → ℂ} {D0 : ℝ}
    (hf : ∫ Ω, ‖f Ω‖ ≤ D0) (p q ξ η : κ → Mom d) :
    ‖∫ b : κ → ℝ, 𝓕 f (toLp 2 b) * ∏ i, cellInt (p i) (q i) (ξ i) (η i) (μ * b i)‖ ≤
      D0 * (μ⁻¹ * cellCa d) ^ Fintype.card κ := by
  have hD0 : 0 ≤ D0 := le_trans (integral_nonneg fun _ => norm_nonneg _) hf
  have hpt : ∀ b : κ → ℝ, ‖𝓕 f (toLp 2 b) * ∏ i, cellInt (p i) (q i) (ξ i) (η i) (μ * b i)‖ₑ ≤
      ENNReal.ofReal D0 * ∏ i, ‖cellInt (p i) (q i) (ξ i) (η i) (μ * b i)‖ₑ := by
    intro b
    rw [enorm_mul, enorm_finset_prod]
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((Real.norm_fourier_le_integral_norm _ _).trans hf)
  have h1 := (enorm_integral_le_lintegral_enorm (μ := (volume : Measure (κ → ℝ))) _).trans
    (lintegral_mono (μ := (volume : Measure (κ → ℝ))) hpt)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    show (volume : Measure (κ → ℝ)) = Measure.pi fun _ => volume from rfl,
    lintegral_fintype_prod_eq_prod (fun i t => ‖cellInt (p i) (q i) (ξ i) (η i) (μ * t)‖ₑ)
      (fun i => ((continuous_cellInt _ _ _ _).comp (continuous_const.mul continuous_id)).enorm.measurable)] at h1
  have h2 : ∏ i, ∫⁻ t, ‖cellInt (p i) (q i) (ξ i) (η i) (μ * t)‖ₑ ≤
      ∏ _i : κ, ENNReal.ofReal (μ⁻¹ * cellCa d) := by
    refine Finset.prod_le_prod fun i _ => (lintegral_cellInt_scale_le (by omega) hμ _ _ _ _).trans ?_
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (le_max_left _ _)
      (inv_nonneg.2 hμ.le))
  have h3 := h1.trans (mul_le_mul_of_nonneg_left h2 zero_le)
  rw [prod_const, card_univ, ← ENNReal.ofReal_pow (by have := one_le_cellCa d; positivity),
    ← ENNReal.ofReal_mul hD0, ← ofReal_norm] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (by have := one_le_cellCa d; positivity)).1 h3

theorem norm_B_sub_Delta_le (hd : 3 ≤ d) {μ : ℝ} (hμ : 0 < μ) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) {f : EuclideanSpace ℝ κ → ℂ} (hfi : Integrable f) {H : ℝ} (hH0 : 0 ≤ H)
    (hH : ∫⁻ Ω, ENNReal.ofReal (wmax θ (fun i => Ω i)) * ‖f Ω‖ₑ ≤ ENNReal.ofReal H)
    (p q ξ η : κ → Mom d) :
    ‖(∫ b : κ → ℝ, 𝓕 f (toLp 2 b) * ∏ i, cellInt (p i) (q i) (ξ i) (η i) (μ * b i)) -
        𝓕 f 0 * ∏ i, ∫ t, cellInt (p i) (q i) (ξ i) (η i) (μ * t)‖ ≤
      4 * Real.pi * H * Fintype.card κ * μ ^ (-θ) * (μ⁻¹ * cellCa d) ^ Fintype.card κ := by
  set T : κ → ℝ → ℂ := fun i t => cellInt (p i) (q i) (ξ i) (η i) (μ * t)
  have hTi : ∀ i, Integrable (T i) := fun i => integrable_cellInt_scale (by omega) hμ _ _ _ _
  have hTc : ∀ i, Continuous (T i) := fun i =>
    (continuous_cellInt _ _ _ _).comp (continuous_const.mul continuous_id)
  have hprodI : Integrable (fun b : κ → ℝ => ∏ i, T i (b i)) :=
    Integrable.fintype_prod (f := T) hTi
  have hFc : Continuous (𝓕 f) := continuous_fourier_of_integrable hfi
  have hFb : ∀ w, ‖𝓕 f w‖ ≤ ∫ Ω, ‖f Ω‖ := fun w => Real.norm_fourier_le_integral_norm _ _
  have hI1 : Integrable (fun b : κ → ℝ => 𝓕 f (toLp 2 b) * ∏ i, T i (b i)) :=
    hprodI.bdd_mul (c := ∫ Ω, ‖f Ω‖) (hFc.comp (PiLp.continuous_toLp 2 _)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun b => hFb _)
  have hΔ : 𝓕 f 0 * ∏ i, ∫ t, T i t = ∫ b : κ → ℝ, 𝓕 f 0 * ∏ i, T i (b i) := by
    rw [integral_const_mul, integral_fintype_prod_volume_eq_prod (f := T)]
  rw [hΔ, ← integral_sub hI1 (hprodI.const_mul _)]
  have hS : ∀ b : κ → ℝ, 0 ≤ 4 * Real.pi * (∑ i, |b i| ^ θ) * H := fun b =>
    mul_nonneg (mul_nonneg (by positivity) (sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _)) hH0
  have hpt : ∀ b : κ → ℝ, ‖𝓕 f (toLp 2 b) * ∏ i, T i (b i) - 𝓕 f 0 * ∏ i, T i (b i)‖ₑ ≤
      ∑ l, ENNReal.ofReal (4 * Real.pi * H) * ∏ i, (if i = l then ENNReal.ofReal (|b i| ^ θ) * ‖T i (b i)‖ₑ
        else ‖T i (b i)‖ₑ) := by
    intro b
    rw [← sub_mul, enorm_mul, enorm_finset_prod]
    have hh := norm_fourier_sub_fourier_zero_le hfi hθ0 hθ1 hH0 hH (toLp 2 b)
    have hh' : ‖𝓕 f (toLp 2 b) - 𝓕 f 0‖ₑ ≤ ENNReal.ofReal (4 * Real.pi * (∑ i, |b i| ^ θ) * H) := by
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (by simpa using hh)
    refine (mul_le_mul_of_nonneg_right hh' zero_le).trans (le_of_eq ?_)
    rw [show 4 * Real.pi * (∑ i, |b i| ^ θ) * H = ∑ l, 4 * Real.pi * H * |b l| ^ θ by
      rw [mul_assoc, mul_comm (∑ i, _) H, ← mul_assoc, mul_sum],
      ENNReal.ofReal_sum_of_nonneg fun l _ => mul_nonneg (by positivity) (Real.rpow_nonneg (abs_nonneg _) _),
      sum_mul]
    refine sum_congr rfl fun l _ => ?_
    rw [prod_ite_mul_eq l (fun i => ENNReal.ofReal (|b i| ^ θ)) (fun i => ‖T i (b i)‖ₑ),
      ENNReal.ofReal_mul (by positivity), mul_assoc]
  have hmeas : ∀ l i, Measurable (fun t : ℝ => if i = l then ENNReal.ofReal (|t| ^ θ) * ‖T i t‖ₑ
      else ‖T i t‖ₑ) := by
    intro l i
    split_ifs
    · exact (ENNReal.measurable_ofReal.comp (continuous_abs.rpow_const
        (fun _ => Or.inr hθ0.le)).measurable).mul (hTc i).enorm.measurable
    · exact (hTc i).enorm.measurable
  have hint_l : ∀ l, ∫⁻ b : κ → ℝ, ENNReal.ofReal (4 * Real.pi * H) * ∏ i, (if i = l then
      ENNReal.ofReal (|b i| ^ θ) * ‖T i (b i)‖ₑ else ‖T i (b i)‖ₑ) ≤
      ENNReal.ofReal (4 * Real.pi * H * (μ ^ (-θ) * (μ⁻¹ * cellCa d) ^ Fintype.card κ)) := by
    intro l
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      show (volume : Measure (κ → ℝ)) = Measure.pi fun _ => volume from rfl,
      lintegral_fintype_prod_eq_prod _ (hmeas l)]
    have hb : ∀ i, ∫⁻ t, (if i = l then ENNReal.ofReal (|t| ^ θ) * ‖T i t‖ₑ else ‖T i t‖ₑ) ≤
        ENNReal.ofReal (if i = l then μ ^ (-θ) * (μ⁻¹ * cellCa d) else μ⁻¹ * cellCa d) := by
      intro i
      split_ifs
      · refine (lintegral_rpow_cellInt_scale_le hd hμ hθ0.le hθ1 _ _ _ _).trans
          (ENNReal.ofReal_le_ofReal ?_)
        rw [show μ⁻¹ * μ ^ (-θ) * (cellK0 d * NTSP.sInt (d - 1)) =
          μ ^ (-θ) * (μ⁻¹ * (cellK0 d * NTSP.sInt (d - 1))) by ring]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hμ.le))
          (Real.rpow_nonneg hμ.le _)
        exact (le_max_left _ _).trans (le_max_right _ _)
      · refine (lintegral_cellInt_scale_le (by omega) hμ _ _ _ _).trans (ENNReal.ofReal_le_ofReal ?_)
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) (inv_nonneg.2 hμ.le)
    have hCa := one_le_cellCa d
    calc ENNReal.ofReal (4 * Real.pi * H) * ∏ i, ∫⁻ t, (if i = l then
          ENNReal.ofReal (|t| ^ θ) * ‖T i t‖ₑ else ‖T i t‖ₑ)
        ≤ ENNReal.ofReal (4 * Real.pi * H) * ∏ i, ENNReal.ofReal
            (if i = l then μ ^ (-θ) * (μ⁻¹ * cellCa d) else μ⁻¹ * cellCa d) :=
          mul_le_mul_of_nonneg_left (Finset.prod_le_prod fun i _ => hb i) zero_le
      _ = ENNReal.ofReal (4 * Real.pi * H) * ENNReal.ofReal (∏ i,
            (if i = l then μ ^ (-θ) * (μ⁻¹ * cellCa d) else μ⁻¹ * cellCa d)) := by
          rw [ENNReal.ofReal_prod_of_nonneg fun i _ => by split_ifs <;> positivity]
      _ = ENNReal.ofReal (4 * Real.pi * H * ∏ i,
            (if i = l then μ ^ (-θ) * (μ⁻¹ * cellCa d) else μ⁻¹ * cellCa d)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ = _ := by
          congr 2
          rw [← mul_prod_erase univ _ (mem_univ l)]
          simp only [ite_true]
          rw [prod_congr rfl fun i hi => (by simp [ne_of_mem_erase hi] :
              (if i = l then μ ^ (-θ) * (μ⁻¹ * cellCa d) else μ⁻¹ * cellCa d) = μ⁻¹ * cellCa d),
            prod_const, card_erase_of_mem (mem_univ l), card_univ, mul_assoc, ← pow_succ']
          congr 2
          have : 0 < Fintype.card κ := Fintype.card_pos_iff.2 ⟨l⟩
          omega
  have hsum : ∫⁻ b : κ → ℝ, ∑ l, ENNReal.ofReal (4 * Real.pi * H) * ∏ i, (if i = l then
      ENNReal.ofReal (|b i| ^ θ) * ‖T i (b i)‖ₑ else ‖T i (b i)‖ₑ) ≤
      ∑ _l : κ, ENNReal.ofReal (4 * Real.pi * H * (μ ^ (-θ) * (μ⁻¹ * cellCa d) ^ Fintype.card κ)) := by
    rw [lintegral_finsetSum (f := fun l (b : κ → ℝ) => ENNReal.ofReal (4 * Real.pi * H) *
      ∏ i, (if i = l then ENNReal.ofReal (|b i| ^ θ) * ‖T i (b i)‖ₑ else ‖T i (b i)‖ₑ))
      _ fun l _ => measurable_const.mul (Finset.measurable_prod _
        fun i _ => (hmeas l i).comp (measurable_pi_apply i))]
    exact sum_le_sum fun l _ => hint_l l
  have htot := (enorm_integral_le_lintegral_enorm (μ := (volume : Measure (κ → ℝ))) _).trans
    ((lintegral_mono (μ := (volume : Measure (κ → ℝ))) hpt).trans hsum)
  have hpos : 0 ≤ 4 * Real.pi * H * (μ ^ (-θ) * (μ⁻¹ * cellCa d) ^ Fintype.card κ) := by
    have := one_le_cellCa d; have := Real.rpow_nonneg hμ.le (-θ); positivity
  rw [← ENNReal.ofReal_sum_of_nonneg fun l _ => hpos, sum_const, card_univ, nsmul_eq_mul,
    ← ofReal_norm] at htot
  refine (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 htot |>.trans (le_of_eq ?_)
  ring

end WaveTurbulence.ApproxNT
