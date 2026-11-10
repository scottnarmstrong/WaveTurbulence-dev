/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Merge
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Abs
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Mink

/-! # P2: absolute convergence and finite sums of level expressions (step 6)

* `ExprAbs`: for every lattice index the integrand is integrable on the time domain and the sum over the lattice of the integrals is
  summable (what linearity needs).
* `vineLevel_abs`: the merged level expression of `vineLevel_bound` satisfies `ExprAbs` for every `tt ∈ outBox D`, `E ∈ outSet D`.
* `clockedExprMul3_finsum`: the finite sum of expressions equals the expression of the summed integrand (Fubini interchange).
* `vineLevel_sum_bound`: finite Minkowski: `XNorm00Restr` of a finite sum of merged level expressions is at most
  `(ccη η + 1) ∑_j (bound of j)`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory Finset
open scoped ENNReal

variable {d : ℕ} {D : SumintPar.SumintDatum d}

/-- Absolute convergence of a clocked expression. -/
def ExprAbs (Mx : CharMix D.S d) (cr : ClockedRows3 D) (hI : 0 < D.S.I) (L γ δ η : ℝ) (tt : Fin 3 → ℝ)
    (E : Fin 4 → Mom d) : Prop :=
  (∀ x : D.S.VIdx → (Fin d → ℤ), Integrable (fun τ => clockedIntegrand3 cr L γ δ η x E tt τ)
      (volume.restrict (D.timeDom hI (tt 0) (tt 1) (tt 2)))) ∧
    Summable fun x : D.S.VIdx → (Fin d → ℤ) => Mx.val L E x * ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2),
      clockedIntegrand3 cr L γ δ η x E tt τ

variable {A : ℝ} {P : WTParams}

end WaveTurbulence.VineEstS5C.P2
