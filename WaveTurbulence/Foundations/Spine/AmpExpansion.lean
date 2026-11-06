/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Sumint.FiniteWeightExpansion
public import WaveTurbulence.Foundations.Sumint.WeightPartitionIdentity
public import WaveTurbulence.Foundations.Sumint.LocalizationBox
/-! # Fourier expansion of a product of unit-ball amplitudes (S3b LADDER-DECAY)

Each source amplitude `F_b` is `SNorm (30 d) 0 ≤ 1` and supported in a unit ball.  A finite
partition into at most `7^d` localized cells expands the product of amplitudes into modulations,
with total coefficient mass at most `(7^d cellFourierFactor d)^{#bonds}`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset MeasureTheory WaveTurbulence WaveTurbulence.Sumint
open scoped FourierTransform ENNReal

variable {d : ℕ}

/-- The finite family of localization cells meeting the unit ball around `c`. -/
noncomputable def cellsAround (c : Mom d) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun i => Finset.Icc (⌈2 * c i - 3⌉) (⌊2 * c i + 3⌋))

lemma card_cellsAround (c : Mom d) : (cellsAround c).card ≤ 7 ^ d := by
  rw [cellsAround, Fintype.card_piFinset]
  calc ∏ i : Fin d, (Finset.Icc (⌈2 * c i - 3⌉) (⌊2 * c i + 3⌋)).card ≤ ∏ _i : Fin d, 7 := by
        apply Finset.prod_le_prod
        intro i _
        rw [Int.card_Icc]
        have h1 := Int.floor_le (2 * c i + 3)
        have h2 := Int.le_ceil (2 * c i - 3)
        have h3 : (⌊2 * c i + 3⌋ : ℝ) + 1 - ⌈2 * c i - 3⌉ ≤ 7 := by linarith
        have h4 : ⌊2 * c i + 3⌋ + 1 - ⌈2 * c i - 3⌉ ≤ 7 := by exact_mod_cast h3
        omega
    _ = 7 ^ d := by simp

lemma localizedWeight_eq_zero_of_not_mem_cells {F : Mom d → ℂ} {c : Mom d}
    (hsupp : ∀ x, 1 < ‖x - c‖ → F x = 0) {a : Fin d → ℤ} (ha : a ∉ cellsAround c) (x : Mom d) :
    localizedWeight a F x = 0 := by
  by_cases hx : 1 < ‖x - c‖
  · simp [localizedWeight, hsupp x hx]
  · push Not at hx
    by_contra hne
    apply ha
    have hp : localizationProfile a x ≠ 0 := by
      intro h; apply hne; simp [localizedWeight, h]
    have hb : ∀ i, |2 * x i - (a i : ℝ)| < 1 := fun i =>
      ApproxNT.abs_lt_one_of_thetaMom_ne_zero hp i
    rw [cellsAround, Fintype.mem_piFinset]
    intro i
    have hci : |x i - c i| ≤ 1 := by
      have : |(x - c) i| ≤ ‖x - c‖ := by
        simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (x - c) i
      simpa using this.trans hx
    have h1 := abs_lt.mp (hb i)
    have h2 := abs_le.mp hci
    rw [Finset.mem_Icc]
    constructor
    · apply Int.ceil_le.mpr
      have : (2 * c i - 3) ≤ (a i : ℝ) := by linarith
      exact this
    · apply Int.le_floor.mpr
      have : (a i : ℝ) ≤ 2 * c i + 3 := by linarith
      exact this


variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The product of amplitudes is a finite sum of modulation integrals. -/
theorem amp_expansion (hd : 1 ≤ d) (F : ι → Mom d → ℂ) (c : ι → Mom d)
    (hF : ∀ b, SNorm (30 * d) 0 (F b) ≤ ENNReal.ofReal 1)
    (hsupp : ∀ b x, 1 < ‖x - c b‖ → F b x = 0) (q : ι → Mom d) :
    ∏ b, F b (q b) = ∑ a ∈ Fintype.piFinset (fun b => cellsAround (c b)),
      ∫ ξ : ι → Mom d, ∏ b, ((Real.fourierChar (inner ℝ (ξ b) (q b)) : ℂ) *
        𝓕 (localizedWeight (a b) (F b)) (ξ b)) := by
  classical
  have hexp : ∀ a : ι → Fin d → ℤ, (∫ ξ : ι → Mom d, ∏ b, ((Real.fourierChar (inner ℝ (ξ b) (q b)) : ℂ) *
        𝓕 (localizedWeight (a b) (F b)) (ξ b))) = ∏ b, localizedWeight (a b) (F b) (q b) :=
    fun a => finite_localizedWeight_expansion (N := 30 * d) (by omega) (by omega)
      (fun _ => 0) F (fun _ => 1) (fun _ => zero_le_one) hF a q
  simp_rw [hexp]
  rw [← tsum_product_localizedWeight F q]
  apply tsum_eq_sum
  intro a ha
  rw [Fintype.mem_piFinset] at ha
  push Not at ha
  obtain ⟨b, hb⟩ := ha
  exact Finset.prod_eq_zero (Finset.mem_univ b)
    (localizedWeight_eq_zero_of_not_mem_cells (hsupp b) hb _)

omit [DecidableEq ι] in
/-- Coefficient mass of the expansion of a product of amplitudes. -/
theorem amp_expansion_mass (hd : 1 ≤ d) (F : ι → Mom d → ℂ)
    (hF : ∀ b, SNorm (30 * d) 0 (F b) ≤ ENNReal.ofReal 1) (a : ι → Fin d → ℤ) :
    Integrable (fun ξ : ι → Mom d => ∏ b, 𝓕 (localizedWeight (a b) (F b)) (ξ b)) ∧
    (∫ ξ : ι → Mom d, ‖∏ b, 𝓕 (localizedWeight (a b) (F b)) (ξ b)‖) ≤
      cellFourierFactor d ^ Fintype.card ι := by
  refine ⟨integrable_tensor_localized_fourier (N := 30 * d) (by omega) (by omega)
    (fun _ => 0) F (fun _ => 1) (fun _ => zero_le_one) hF a, ?_⟩
  have h := integral_norm_tensor_localized_fourier_le (N := 30 * d) (by omega) (by omega)
    (fun _ => 0) F (fun _ => 1) (fun _ => zero_le_one) hF a
  simpa using h

end WaveTurbulence.LadderDecay
