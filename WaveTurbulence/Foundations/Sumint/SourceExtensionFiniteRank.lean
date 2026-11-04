/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.PhaseCellExtension

/-!
# The actual ambient extension has finite rank in the independent input frequencies

The finite support is fixed before choosing any frequencies or output
times. Each time coefficient is genuinely integrable. This identity is
used only for Fubini and measurability, not to estimate oscillatory gains.
-/

public section
open MeasureTheory
namespace WaveTurbulence.Sumint

/-- The actual weighted source extension is a finite character expansion with fixed time factors. -/
theorem weightedSourceExtension_eq_sum {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (N : ℕ) (h : ℝ) {L : ℝ} (hL : 0 < L) (γ δ η : ℝ) (hη : η ≤ 1/3)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t : Fin 3 → ℝ) :
    weightedSourceExtension D hI N h L γ δ η p ν r t =
      ∑ x ∈ inputCutoffBox L p,
        ((sourceWeightDecay D L γ η*
          ‖r‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card : ℝ):ℂ)*
        ((∏ v, inputCutoff (p v) (latticePoint L (x v)) : ℝ):ℂ)*
          inputCharacter D L ν x * phaseCellExtension D hI N h L γ δ η x r t := by
  classical
  let C : ℂ := ((sourceWeightDecay D L γ η*
    ‖r‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card : ℝ):ℂ)
  let a := fun x : D.S.VIdx → Fin d → ℤ =>
    C*((∏ v, inputCutoff (p v) (latticePoint L (x v)) : ℝ):ℂ)*inputCharacter D L ν x
  have he : weightedCutoffInput D L γ δ η p ν r = fun u =>
      ∑ x ∈ inputCutoffBox L p, a x*D.phase L γ δ η x r 0 u := by
    funext u
    unfold weightedCutoffInput
    rw [cutoffPhaseSum_eq_sum D hL γ δ η p ν r 0 u,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    dsimp [a,C]
    ring
  unfold weightedSourceExtension
  rw [he,timeCellExtension_finsetSum D hI N h (inputCutoffBox L p) _
    (fun x _ j => (integrableOn_phase_localDomain D L γ δ η hη x r 0 ((j:ℝ)*h) h).const_mul (a x))]
  simp_rw [timeCellExtension_const_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  dsimp [a,C,phaseCellExtension,sourceOutputModulation]
  ring

end WaveTurbulence.Sumint
