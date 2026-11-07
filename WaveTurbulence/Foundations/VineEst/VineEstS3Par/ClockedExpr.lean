/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ClockPhase
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.SignedBound
public import WaveTurbulence.Foundations.SumintPar.Data

/-! # Clock-dependent weights in `sumint` form and the mode data (engine definitions)

`clockedExpr` is the `sumint` expression `∑ₓ ∫ signedPhase · ∏ᵨ Wᵨ(clockᵨ)(momentumᵨ)` whose weights are
functions of two clocks.  `modeDatum` is the datum with time-independent weights `c ρ` and parameters shifted
by a mode `Δ`; `signedExpr (modeDatum ..)` is the corresponding `sumint` expression.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.SumintPar WaveTurbulence.VineEstS3.FS Finset
  MeasureTheory
open scoped ENNReal

variable {d : ℕ} (D : SumintPar.SumintDatum d)

/-- The momentum of a weight row at the input vector `x` and boundary vector `E`. -/
noncomputable def rowMom (L : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (E : Fin 4 → Mom d) : Row D → Mom d :=
  Sum.elim (D.kVec L x E) (D.ℓVec L x E)

/-- Clock-dependent weights: a function of a clock pair, of the output difference `r = e - f` and of the row
momentum, and the two slots of the clock pair.  The `ℒ` rows do not depend on `r`. -/
structure ClockedRows where
  W : Row D → (Fin 2 → ℝ) → Mom d → Mom d → ℂ
  slot : Row D → Fin 2 → Slot D
  W_indep : ∀ (v : D.S.VIdx) (c : Fin 2 → ℝ) (r r' k : Mom d), W (Sum.inr v) c r k = W (Sum.inr v) c r' k

variable {D}

/-- The clock pair of row `ρ`. -/
def ClockedRows.clock (cr : ClockedRows D) (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ) (ρ : Row D) : Fin 2 → ℝ :=
  fun i => slotVal D τ tt (cr.slot ρ i)

/-- The integrand of the clocked `sumint` expression. -/
noncomputable def clockedIntegrand (cr : ClockedRows D)
    (L γ δ η : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (E : Fin 4 → Mom d) (tt : Fin 3 → ℝ)
    (τ : D.S.TVar → ℝ) : ℂ :=
  D.phase L γ δ η x (E 0 - E 1) (tt 0) τ *
    ∏ ρ, cr.W ρ (cr.clock τ tt ρ) (E 0 - E 1) (rowMom D L x E ρ)

/-- The clocked `sumint` expression, with the factor `|r|` for each bad block of case (b) (as in `SumintDatum.expr`). -/
noncomputable def clockedExpr (cr : ClockedRows D)
    (hI : 0 < D.S.I) (L γ δ η : ℝ) (tt : Fin 3 → ℝ) (E : Fin 4 → Mom d) : ℂ :=
  ((‖E 0 - E 1‖ ^ (Finset.univ.filter fun i => D.S.nor i = false ∧ D.badKind i = 1).card : ℝ) : ℂ) *
  ∑' x : D.S.VIdx → (Fin d → ℤ), ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2),
    clockedIntegrand cr L γ δ η x E tt τ

/-- The datum with time-independent weights `c` (functions of `r` and of the row momentum) and parameters shifted by `Δ`. -/
def modeDatum (D : SumintPar.SumintDatum d) (c : Row D → Mom d → Mom d → ℂ) (Δ : D.S.TVar → ℝ) :
    SumintPar.SumintDatum d :=
  { D with wK := fun v => c (Sum.inl v), wL := fun v => c (Sum.inr v) 0, param := fun v => D.param v + Δ v }

theorem expr_modeDatum (c : Row D → Mom d → Mom d → ℂ)
    (hc : ∀ (v : D.S.VIdx) (r r' k : Mom d), c (Sum.inr v) r k = c (Sum.inr v) r' k) (Δ : D.S.TVar → ℝ) (hI : 0 < D.S.I)
    (L γ δ η : ℝ) (tt : Fin 3 → ℝ) (E : Fin 4 → Mom d) :
    (modeDatum D c Δ).expr hI L γ δ η tt E =
      ((‖E 0 - E 1‖ ^ (Finset.univ.filter fun i => D.S.nor i = false ∧ D.badKind i = 1).card : ℝ) : ℂ) *
      ∑' x : D.S.VIdx → (Fin d → ℤ), (∏ ρ, c ρ (E 0 - E 1) (rowMom D L x E ρ)) *
        ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2), D.phase L γ δ η x (E 0 - E 1) (tt 0) τ * paramFactor D Δ τ := by
  unfold SumintPar.SumintDatum.expr
  refine congrArg₂ (· * ·) rfl (tsum_congr fun x => ?_)
  congr 1
  · rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    change _ * c (Sum.inr v) 0 _ = _ * c (Sum.inr v) (E 0 - E 1) _
    rw [hc v 0 (E 0 - E 1)]
    rfl
  · refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    exact phase_param D Δ L γ δ η x (E 0 - E 1) (tt 0) τ

end WaveTurbulence.VineEstS3Par.Eng
