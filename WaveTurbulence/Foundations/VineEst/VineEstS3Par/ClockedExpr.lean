/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ClockPhase
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

variable {D}

/-- The datum with time-independent weights `c` (functions of `r` and of the row momentum) and parameters shifted by `Δ`. -/
def modeDatum (D : SumintPar.SumintDatum d) (c : Row D → Mom d → Mom d → ℂ) (Δ : D.S.TVar → ℝ) :
    SumintPar.SumintDatum d :=
  { D with wK := fun v => c (Sum.inl v), wL := fun v => c (Sum.inr v) 0, param := fun v => D.param v + Δ v }

end WaveTurbulence.VineEstS3Par.Eng
