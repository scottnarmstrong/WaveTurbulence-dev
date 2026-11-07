/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ClockedExpr
public import WaveTurbulence.Foundations.VineEst.VineEstS3.SNormAux
public import WaveTurbulence.Foundations.VineEst.VineEstS3.RestrScalar

/-! # `sumint` for weights of arbitrary size (engine step SS)

Definitions of the scaled-weight form over the parametric datum (the theorem is `DegenVinePar.scaledSumintMixAt_of`); weights
with `SNorm ≤ s_ρ` for arbitrary `s_ρ ≥ 0` instead of the normalised `L^{-(γ₁-√η) g_ρ}`: the bound acquires the
factor `∏_ρ s_ρ L^{(γ₁-√η) g_ρ}`.  It is a formal consequence of `SumintDoubledAt A P`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.SumintPar WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS Finset
  MeasureTheory
open scoped ENNReal

/-- The exponent `min(2γ, min(1, 2(d-1)(1-γ))) - √η` of the weight bounds. -/
noncomputable def weightExp (d : ℕ) (γ η : ℝ) : ℝ :=
  min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) - Real.sqrt η

/-- The weight-bound clauses of `Admissible`, for explicit weight families (the `𝒦` weights depend on `r`). -/
def WeightBounds {d : ℕ} (D : SumintPar.SumintDatum d) (L γ η : ℝ) (a : D.S.VIdx → Mom d → Mom d → ℂ)
    (b : D.S.VIdx → Mom d → ℂ) : Prop :=
  ∀ v, (∀ r, SNorm D.wN D.wDec (a v r) ≤ ENNReal.ofReal (L ^ (-weightExp d γ η * D.g v))) ∧
    SNorm D.wN 0 (b v) ≤ ENNReal.ofReal (L ^ (-weightExp d γ η * D.g' v))

/-- The datum with the weights replaced (`ℒ` rows do not depend on `r`: the value at `r = 0` is used). -/
abbrev reweight {d : ℕ} (D : SumintPar.SumintDatum d) (w : Row D → Mom d → Mom d → ℂ) : SumintPar.SumintDatum d :=
  { D with wK := fun v => w (Sum.inl v), wL := fun v => w (Sum.inr v) 0 }

/-- The decay multiplicities of the weight rows. -/
def rowG {d : ℕ} (D : SumintPar.SumintDatum d) : Row D → ℕ := Sum.elim D.g D.g'

/-- The size bounds of a weight family (uniform in `r`). -/
def RowBounds {d : ℕ} (D : SumintPar.SumintDatum d) (w : Row D → Mom d → Mom d → ℂ) (s : Row D → ℝ) : Prop :=
  (∀ v r, SNorm D.wN D.wDec (w (Sum.inl v) r) ≤ ENNReal.ofReal (s (Sum.inl v))) ∧
    ∀ v, SNorm D.wN 0 (w (Sum.inr v) 0) ≤ ENNReal.ofReal (s (Sum.inr v))

@[simp] theorem reweight_kVec {d : ℕ} (D : SumintPar.SumintDatum d) (w : Row D → Mom d → Mom d → ℂ) :
    (reweight D w).kVec = D.kVec := rfl

@[simp] theorem reweight_ℓVec {d : ℕ} (D : SumintPar.SumintDatum d) (w : Row D → Mom d → Mom d → ℂ) :
    (reweight D w).ℓVec = D.ℓVec := rfl

/-- The output time box of `sumint`. -/
def outBox {d : ℕ} (D : SumintPar.SumintDatum d) : Set (Fin 3 → ℝ) :=
  {tt | (∀ c, (D.qOut c : ℝ) ≤ tt c ∧ tt c ≤ D.qOut c + 1) ∧ max (tt 1) (tt 2) < tt 0}

/-- The output momentum set of `sumint`. -/
def outSet {d : ℕ} (D : SumintPar.SumintDatum d) (L γ η : ℝ) : Set (Fin 4 → Mom d) :=
  {v | (∀ c, (∃ nv : Fin d → ℤ, v c = D.wBar + latticePoint L nv) ∧ ‖v c - D.centre c‖ ≤ 1) ∧
    v 0 - v 1 = v 3 - v 2 ∧ v 0 ≠ v 1 ∧ ‖v 0 - v 1‖ ≤ L ^ (-γ + η)}

/-- `maxPar`. -/
noncomputable def maxPar {d : ℕ} (D : SumintPar.SumintDatum d) : ℝ :=
  ⨆ v, jbr (d := 1) (WithLp.toLp 2 fun _ => D.param v)

/-- The right-hand side of `sumint`. -/
noncomputable def sumintRHS (P : WTParams) (D : SumintPar.SumintDatum P.d) : ℝ :=
  P.C₁ * maxPar D ^ (P.η ^ 6) * (P.C₁ * P.δ ^ (-(1 : ℝ) / 2)) ^ D.S.M *
    P.L ^ ((D.S.M : ℝ) * (P.d - P.γ) -
      P.η ^ 2 * ((Finset.univ.filter fun i => D.S.nor i = false).card + D.M₁) -
      P.η ^ 8 * D.M₀ + P.η ^ 7)

end WaveTurbulence.VineEstS3Par.Eng
