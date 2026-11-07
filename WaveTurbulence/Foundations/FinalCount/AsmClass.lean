/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmGate
public import WaveTurbulence.Foundations.FinalCount.AsmTopClass3
public import WaveTurbulence.Foundations.FinalCount.AsmArith
/-! **FINALCOUNT-ASSEMBLY (garden wrapper, class labels).**  Counting facts for the split of an admissible set into classes
(tame set × fixed values): at most `2R` atoms have degree `< 4`, and the label set has at most `2^n (2R+1)^{2R}` elements. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]

/-- At most `2R` atoms have degree `< 4`. -/
theorem card_lowdeg_le {R : ℕ} {M₀ : Molecule V D₀} (hS : SubHyp R M₀) :
    (M₀.atoms.filter fun a => M₀.deg a < 4).card ≤ 2 * R := by
  have h1 := sum_deg_eq M₀
  have h2 := card_darts_eq_two_bonds M₀
  have h3 := hS.count
  have hle : ∀ a ∈ M₀.atoms, M₀.deg a ≤ 4 := fun a ha => deg_le_four (M := M₀) (hS.bounds a ha)
  have key : ∑ a ∈ M₀.atoms, (4 - M₀.deg a) = 2 * R := by
    have : ∑ a ∈ M₀.atoms, (4 - M₀.deg a) + ∑ a ∈ M₀.atoms, M₀.deg a = ∑ a ∈ M₀.atoms, 4 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a ha => Nat.sub_add_cancel (hle a ha)
    simp only [Finset.sum_const, smul_eq_mul] at this
    omega
  calc (M₀.atoms.filter fun a => M₀.deg a < 4).card = ∑ a ∈ M₀.atoms.filter (fun a => M₀.deg a < 4), 1 := by simp
    _ ≤ ∑ a ∈ M₀.atoms.filter (fun a => M₀.deg a < 4), (4 - M₀.deg a) := by
        refine Finset.sum_le_sum fun a ha => ?_
        have := (Finset.mem_filter.1 ha).2
        omega
    _ ≤ ∑ a ∈ M₀.atoms, (4 - M₀.deg a) := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = 2 * R := key

/-- **Absorption of the class factor.**  For `R` at most polylogarithmic in `L`, `(a R²)^R ≤ L^{(R-1)/20 + ε}` for large `L`. -/
theorem absorb_Rpow (a : ℝ) (ha : 1 ≤ a) (c : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ L₁ : ℝ, 1 ≤ L₁ ∧ ∀ L ≥ L₁, ∀ R : ℕ, 1 ≤ R → (R : ℝ) ≤ (1 + Real.log L) ^ c →
      (a * (R : ℝ) ^ 2) ^ R ≤ L ^ (((R : ℝ) - 1) / 20 + ε) := by
  obtain ⟨L₀, hL₀, h0⟩ := polylog_absorb a (2 * c) (1 / 40) (by norm_num)
  obtain ⟨L₀', hL₀', h0'⟩ := polylog_absorb a 0 ε hε
  refine ⟨max L₀ L₀', le_trans hL₀ (le_max_left _ _), fun L hL R hR hRc => ?_⟩
  have hLa : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hLb : L₀' ≤ L := le_trans (le_max_right _ _) hL
  have hL1 : 1 ≤ L := le_trans hL₀ hLa
  have hL0 : 0 < L := by linarith
  rcases Nat.lt_or_ge R 2 with hR2 | hR2
  · have hR1 : R = 1 := by omega
    subst hR1
    have := h0' L hLb
    simp at this ⊢
    simpa using this
  · have hRr : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    have hsq : (R : ℝ) ^ 2 ≤ (1 + Real.log L) ^ (2 * c) := by
      rw [pow_mul']
      exact pow_le_pow_left₀ hRr hRc 2
    have h1 : a * (R : ℝ) ^ 2 ≤ L ^ (1 / 40 : ℝ) := by
      calc a * (R : ℝ) ^ 2 ≤ a * (1 + Real.log L) ^ (2 * c) := by gcongr
        _ ≤ L ^ (1 / 40 : ℝ) := h0 L hLa
    have h2 : (a * (R : ℝ) ^ 2) ^ R ≤ (L ^ (1 / 40 : ℝ)) ^ R :=
      pow_le_pow_left₀ (by positivity) h1 R
    have h3 : (L ^ (1 / 40 : ℝ)) ^ R = L ^ ((1 / 40 : ℝ) * R) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    rw [h3] at h2
    refine h2.trans (Real.rpow_le_rpow_of_exponent_le hL1 ?_)
    have : (2 : ℝ) ≤ R := by exact_mod_cast hR2
    linarith

end WaveTurbulence.FinalCountAsm
