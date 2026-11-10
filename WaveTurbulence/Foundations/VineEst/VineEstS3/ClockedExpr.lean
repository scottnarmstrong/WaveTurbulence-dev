/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.ClockPhase
public import WaveTurbulence.Foundations.VineEst.VineEstS3.SignedBound

/-! # Clock-dependent weights in `sumint` form and the mode data (engine definitions)

`clockedExpr` is the `sumint` expression `∑ₓ ∫ signedPhase · ∏ᵨ Wᵨ(clockᵨ)(momentumᵨ)` whose weights are
functions of two clocks.  `modeDatum` is the datum with time-independent weights `c ρ` and parameters shifted
by a mode `Δ`; `signedExpr (modeDatum ..)` is the corresponding `sumint` expression.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.FS Finset
  MeasureTheory
open scoped ENNReal

variable {d : ℕ} (D : SumintDatum d)

/-- The momentum of a weight row at the input vector `x` and boundary vector `E`. -/
noncomputable def rowMom (L : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (E : Fin 4 → Mom d) : Row D → Mom d :=
  Sum.elim (D.kVec L x E) (D.ℓVec L x E)

/-- Clock-dependent weights: a function of a clock pair, and the two slots of the clock pair. -/
structure ClockedRows where
  W : Row D → (Fin 2 → ℝ) → Mom d → ℂ
  slot : Row D → Fin 2 → Slot D

variable {D}

/-- The clock pair of row `ρ`. -/
def ClockedRows.clock (cr : ClockedRows D) (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ) (ρ : Row D) : Fin 2 → ℝ :=
  fun i => slotVal D τ tt (cr.slot ρ i)

/-- The integrand of the clocked `sumint` expression. -/
noncomputable def clockedIntegrand (cr : ClockedRows D) (coreFirstSign coreSign : Fin D.S.I → ℤˣ)
    (L γ δ η : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (E : Fin 4 → Mom d) (tt : Fin 3 → ℝ)
    (τ : D.S.TVar → ℝ) : ℂ :=
  signedPhase D coreFirstSign coreSign L γ δ η x (E 0 - E 1) (tt 0) τ *
    ∏ ρ, cr.W ρ (cr.clock τ tt ρ) (rowMom D L x E ρ)

/-- The datum with time-independent weights `c` and parameters shifted by `Δ`. -/
def modeDatum (D : SumintDatum d) (c : Row D → Mom d → ℂ) (Δ : D.S.TVar → ℝ) : SumintDatum d :=
  { D with wK := fun v => c (Sum.inl v), wL := fun v => c (Sum.inr v),
           param := fun v => D.param v + Δ v }

end WaveTurbulence.VineEstS3.Eng
