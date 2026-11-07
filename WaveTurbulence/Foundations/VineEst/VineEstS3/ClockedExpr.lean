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

/-- The clocked `sumint` expression (the kernel of V4's endpoint without `ε` and bad factors). -/
noncomputable def clockedExpr (cr : ClockedRows D) (coreFirstSign coreSign : Fin D.S.I → ℤˣ)
    (hI : 0 < D.S.I) (L γ δ η : ℝ) (tt : Fin 3 → ℝ) (E : Fin 4 → Mom d) : ℂ :=
  ∑' x : D.S.VIdx → (Fin d → ℤ), ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2),
    clockedIntegrand cr coreFirstSign coreSign L γ δ η x E tt τ

/-- The datum with time-independent weights `c` and parameters shifted by `Δ`. -/
def modeDatum (D : SumintDatum d) (c : Row D → Mom d → ℂ) (Δ : D.S.TVar → ℝ) : SumintDatum d :=
  { D with wK := fun v => c (Sum.inl v), wL := fun v => c (Sum.inr v),
           param := fun v => D.param v + Δ v }

theorem signedExpr_modeDatum (hno : ∀ i, D.badKind i ≠ 1) (c : Row D → Mom d → ℂ) (Δ : D.S.TVar → ℝ)
    (coreFirstSign coreSign : Fin D.S.I → ℤˣ) (hI : 0 < D.S.I) (L γ δ η : ℝ) (tt : Fin 3 → ℝ)
    (E : Fin 4 → Mom d) :
    signedExpr (modeDatum D c Δ) coreFirstSign coreSign hI L γ δ η tt E =
      ∑' x : D.S.VIdx → (Fin d → ℤ), (∏ ρ, c ρ (rowMom D L x E ρ)) *
        ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2),
          signedPhase D coreFirstSign coreSign L γ δ η x (E 0 - E 1) (tt 0) τ * paramFactor D Δ τ := by
  unfold signedExpr
  have h0 : (Finset.univ.filter fun i => (modeDatum D c Δ).S.nor i = false ∧
      (modeDatum D c Δ).badKind i = 1).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ h
    exact hno i h.2
  simp only [h0, pow_zero, Complex.ofReal_one, one_mul]
  refine tsum_congr fun x => ?_
  congr 1
  · rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
    rfl
  · refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    · exact (signedPhase_param { D with wK := fun v => c (Sum.inl v), wL := fun v => c (Sum.inr v) } Δ
        coreFirstSign coreSign L γ δ η x (E 0 - E 1) (tt 0) τ)

end WaveTurbulence.VineEstS3.Eng
