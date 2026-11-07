/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.Mink
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ScaledSumint

/-! # Small facts for the engine assembly -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS MeasureTheory Set
open scoped ENNReal

theorem cc_translate {r : ℕ} (θ : ℝ) (q : Fin r → ℝ) :
    cutoffMultiplierConstant θ (cutQ q) = cutoffMultiplierConstant θ (cutQ (0 : Fin r → ℝ)) := by
  unfold cutoffMultiplierConstant
  rw [cutQ_eq_translate q]
  rw [timeFourierNorm_translate]

/-- The `η`-dependent cutoff constant. -/
noncomputable def ccη (η : ℝ) : ℝ≥0∞ := cutoffMultiplierConstant (2 * η ^ 8) (cutQ (0 : Fin 3 → ℝ))

/-- The part of `sumintRHS` not depending on the parameters. -/
noncomputable def sumintRHS0 (P : WTParams) {d : ℕ} (D : SumintDatum d) : ℝ :=
  P.C₁ * (P.C₁ * P.δ ^ (-(1 : ℝ) / 2)) ^ D.S.M *
    P.L ^ ((D.S.M : ℝ) * (P.d - P.γ) -
      P.η ^ 2 * ((Finset.univ.filter fun i => D.S.nor i = false).card + D.M₁) -
      P.η ^ 8 * D.M₀ + P.η ^ 7)

theorem sumintRHS_eq (P : WTParams) (D : SumintDatum P.d) :
    sumintRHS P D = maxPar D ^ (P.η ^ 6) * sumintRHS0 P D := by
  unfold sumintRHS sumintRHS0
  ring

theorem outBox_subset_cell {d : ℕ} (D : SumintDatum d) : outBox D ⊆ cell (fun c => (D.qOut c : ℝ)) := by
  intro tt htt c
  exact htt.1 c

theorem countable_outSet {d : ℕ} (D : SumintDatum d) (L γ η : ℝ) : (outSet D L γ η).Countable := by
  refine Set.Countable.mono ?_ (Set.countable_range
    (fun n : Fin 4 → Fin d → ℤ => fun c : Fin 4 => D.wBar + latticePoint L (n c)))
  intro v hv
  choose nv hnv using fun c => (hv.1 c).1
  exact ⟨nv, funext fun c => (hnv c).symm⟩

end WaveTurbulence.VineEstS3.Eng
