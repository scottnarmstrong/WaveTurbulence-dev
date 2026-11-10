/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.DegenVinePar.MixCounted
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ClockedExpand

/-! # The multiplied clocked `sumint` expression and its mode expansion (DEGEN-VINE)

`clockedExprMul` is V5's `clockedExpr` with the lattice sum weighted by a character mixture; the interchange of
the lattice sum and the Fourier mode series is as in `VineEstS3.Eng.clockedExpr_hasSum`, with the bounded factor
`M.val L E x` carried along.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.DegenVinePar
open WaveTurbulence.DegenVine
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.SumintPar WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS3Par.Eng Finset MeasureTheory
open scoped ENNReal

variable {d : ℕ} {D : SumintPar.SumintDatum d}

theorem exprMix_modeDatum (M : CharMix D.S d)
    (c : Row D → Mom d → Mom d → ℂ)
    (hc : ∀ (v : D.S.VIdx) (r r' k : Mom d), c (Sum.inr v) r k = c (Sum.inr v) r' k) (Δ : D.S.TVar → ℝ)
    (hI : 0 < D.S.I) (L γ δ η : ℝ) (tt : Fin 3 → ℝ)
    (E : Fin 4 → Mom d) :
    exprMix (D := modeDatum D c Δ) M hI L γ δ η tt E =
      ((‖E 0 - E 1‖ ^ (Finset.univ.filter fun i => D.S.nor i = false ∧ D.badKind i = 1).card : ℝ) : ℂ) *
      ∑' x : D.S.VIdx → (Fin d → ℤ), M.val L E x * ((∏ ρ, c ρ (E 0 - E 1) (rowMom D L x E ρ)) *
        ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2), D.phase L γ δ η x (E 0 - E 1) (tt 0) τ * paramFactor D Δ τ) := by
  unfold exprMix
  refine congrArg₂ (· * ·) rfl (tsum_congr fun x => ?_)
  rw [mul_assoc]
  congr 2
  · rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    change _ * c (Sum.inr v) 0 _ = _ * c (Sum.inr v) (E 0 - E 1) _
    rw [hc v 0 (E 0 - E 1)]
    rfl
  · refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    exact phase_param D Δ L γ δ η x (E 0 - E 1) (tt 0) τ


end WaveTurbulence.DegenVinePar
