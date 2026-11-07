/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceFactorProduct
public import WaveTurbulence.Foundations.SumintPar.SourceFactorSupport

/-!
# Exact factorization of the actual cutoff source lattice sum

The source lattice is reindexed by a genuine equivalence and every
factor has a fixed finite support. Thus the factorization is an identity
of the original complex sums, before taking absolute values.
-/

@[expose] public section
set_option autoImplicit false

open Finset

namespace WaveTurbulence.SumintPar

/-- The literal source lattice sum is its zero-input phase times the
product of its independent linear, pair and normal lattice sums. -/
theorem cutoffPhaseSum_eq_prod_factors {d : ℕ} (D : SumintDatum d) {L : ℝ}
    (hL : 0 < L) (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) :
    cutoffPhaseSum D L γ δ η p ν r t τ =
      D.phase L γ δ η (fun _ => 0) r t τ *
        ∏ a : FactorIdx D.S, ∑' n : FactorInput D.S (Fin d → ℤ) a,
          sourceFactorTerm D L γ δ p ν r t τ a n := by
  classical
  have hp (x : D.S.VIdx → Fin d → ℤ) :
      ((∏ v, inputCutoff (p v) (latticePoint L (x v)) : ℝ) : ℂ)*
        inputCharacter D L ν x*D.phase L γ δ η x r t τ =
      D.phase L γ δ η (fun _ => 0) r t τ *
        ∏ a : FactorIdx D.S, sourceFactorTerm D L γ δ p ν r t τ a
          (inputFactorEquiv D.S (Fin d → ℤ) x a) := by
    rw [prod_sourceFactorTerm_at_input,phase_eq_zero_mul_spatialCharacter]
    ring
  unfold cutoffPhaseSum
  calc
    _ = ∑' x : D.S.VIdx → Fin d → ℤ,
        D.phase L γ δ η (fun _ => 0) r t τ *
          ∏ a : FactorIdx D.S, sourceFactorTerm D L γ δ p ν r t τ a
            (inputFactorEquiv D.S (Fin d → ℤ) x a) := tsum_congr hp
    _ = D.phase L γ δ η (fun _ => 0) r t τ *
        ∑' x : D.S.VIdx → Fin d → ℤ,
          ∏ a : FactorIdx D.S, sourceFactorTerm D L γ δ p ν r t τ a
            (inputFactorEquiv D.S (Fin d → ℤ) x a) := tsum_mul_left
    _ = D.phase L γ δ η (fun _ => 0) r t τ *
        ∑' z : (a : FactorIdx D.S) → FactorInput D.S (Fin d → ℤ) a,
          ∏ a : FactorIdx D.S, sourceFactorTerm D L γ δ p ν r t τ a (z a) :=
      congrArg (fun w : ℂ => D.phase L γ δ η (fun _ => 0) r t τ*w)
        ((inputFactorEquiv D.S (Fin d → ℤ)).tsum_eq
          (fun z => ∏ a : FactorIdx D.S, sourceFactorTerm D L γ δ p ν r t τ a (z a)))
    _ = _ := by
      rw [tsum_product_eq_product_tsum (sourceFactorSupport D L p)
        (sourceFactorTerm D L γ δ p ν r t τ)
        (fun a n hn => sourceFactorTerm_eq_zero_of_not_support D hL γ δ p ν r t τ a n hn)]

/-- Taking the norm after exact factorization preserves all oscillatory cancellation. -/
theorem norm_cutoffPhaseSum_eq_prod_factors {d : ℕ} (D : SumintDatum d) {L : ℝ}
    (hL : 0 < L) (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) :
    ‖cutoffPhaseSum D L γ δ η p ν r t τ‖ =
      ‖D.phase L γ δ η (fun _ => 0) r t τ‖ *
        ∏ a : FactorIdx D.S, ‖∑' n : FactorInput D.S (Fin d → ℤ) a,
          sourceFactorTerm D L γ δ p ν r t τ a n‖ := by
  rw [cutoffPhaseSum_eq_prod_factors D hL γ δ η p ν r t τ,norm_mul,norm_prod]

end WaveTurbulence.SumintPar
