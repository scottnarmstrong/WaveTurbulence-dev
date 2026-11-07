/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.SumintDoubled
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ClockedExpr
public import WaveTurbulence.Foundations.VineEst.VineEstS3.SNormAux
public import WaveTurbulence.Foundations.VineEst.VineEstS3.RestrScalar

/-! # `sumint` for weights of arbitrary size (engine step SS)

`ScaledSumintAt A P` is the pointwise (at a parameter tuple `P`) form of `SumintSignedDoubled` extended to weights
with `SNorm ≤ s_ρ` for arbitrary `s_ρ ≥ 0` instead of the normalised `L^{-(γ₁-√η) g_ρ}`: the bound acquires the
factor `∏_ρ s_ρ L^{(γ₁-√η) g_ρ}`.  It is a formal consequence of `SumintDoubledAt A P`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.Eng
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS Finset
  MeasureTheory
open scoped ENNReal

/-- The exponent `min(2γ, min(1, 2(d-1)(1-γ))) - √η` of the weight bounds. -/
noncomputable def weightExp (d : ℕ) (γ η : ℝ) : ℝ :=
  min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) - Real.sqrt η

/-- The weight-bound clauses of `Admissible`, for explicit weight families. -/
def WeightBounds {d : ℕ} (D : SumintDatum d) (L γ η : ℝ) (a b : D.S.VIdx → Mom d → ℂ) : Prop :=
  ∀ v, SNorm (30 * d) (30 * d) (a v) ≤ ENNReal.ofReal (L ^ (-weightExp d γ η * D.g v)) ∧
    SNorm (30 * d) 0 (b v) ≤ ENNReal.ofReal (L ^ (-weightExp d γ η * D.g' v))

/-- The datum with the weights replaced. -/
abbrev reweight {d : ℕ} (D : SumintDatum d) (w : Row D → Mom d → ℂ) : SumintDatum d :=
  { D with wK := fun v => w (Sum.inl v), wL := fun v => w (Sum.inr v) }

/-- The decay multiplicities of the weight rows. -/
def rowG {d : ℕ} (D : SumintDatum d) : Row D → ℕ := Sum.elim D.g D.g'

/-- The size bounds of a weight family. -/
def RowBounds {d : ℕ} (D : SumintDatum d) (w : Row D → Mom d → ℂ) (s : Row D → ℝ) : Prop :=
  (∀ v, SNorm (30 * d) (30 * d) (w (Sum.inl v)) ≤ ENNReal.ofReal (s (Sum.inl v))) ∧
    ∀ v, SNorm (30 * d) 0 (w (Sum.inr v)) ≤ ENNReal.ofReal (s (Sum.inr v))

@[simp] theorem reweight_kVec {d : ℕ} (D : SumintDatum d) (w : Row D → Mom d → ℂ) :
    (reweight D w).kVec = D.kVec := rfl

@[simp] theorem reweight_ℓVec {d : ℕ} (D : SumintDatum d) (w : Row D → Mom d → ℂ) :
    (reweight D w).ℓVec = D.ℓVec := rfl

theorem signedExpr_reweight_scale {d : ℕ} (D : SumintDatum d) (n : Row D → ℂ) (w : Row D → Mom d → ℂ)
    (cfs cs : Fin D.S.I → ℤˣ) (hI : 0 < D.S.I) (L γ δ η : ℝ) (tt : Fin 3 → ℝ) (E : Fin 4 → Mom d) :
    signedExpr (reweight D (fun ρ k => n ρ * w ρ k)) cfs cs hI L γ δ η tt E =
      (∏ ρ, n ρ) * signedExpr (reweight D w) cfs cs hI L γ δ η tt E := by
  unfold signedExpr
  have hp : ∀ x : D.S.VIdx → (Fin d → ℤ),
      (∏ v, (reweight D (fun ρ k => n ρ * w ρ k)).wK v ((reweight D (fun ρ k => n ρ * w ρ k)).kVec L x E v) *
        (reweight D (fun ρ k => n ρ * w ρ k)).wL v
          ((reweight D (fun ρ k => n ρ * w ρ k)).ℓVec L x E v)) =
      (∏ ρ, n ρ) * ∏ v, (reweight D w).wK v ((reweight D w).kVec L x E v) *
        (reweight D w).wL v ((reweight D w).ℓVec L x E v) := by
    intro x
    simp only [Fintype.prod_sum_type, Finset.prod_mul_distrib, reweight_kVec, reweight_ℓVec]
    ring
  simp only [hp]
  have h2 : (∑' x : D.S.VIdx → (Fin d → ℤ), ((∏ ρ, n ρ) * ∏ v, (reweight D w).wK v ((reweight D w).kVec L x E v) *
        (reweight D w).wL v ((reweight D w).ℓVec L x E v)) *
      ∫ τ in (reweight D w).timeDom hI (tt 0) (tt 1) (tt 2),
        signedPhase (reweight D w) cfs cs L γ δ η x (E 0 - E 1) (tt 0) τ) =
      (∏ ρ, n ρ) * ∑' x : D.S.VIdx → (Fin d → ℤ), (∏ v, (reweight D w).wK v ((reweight D w).kVec L x E v) *
        (reweight D w).wL v ((reweight D w).ℓVec L x E v)) *
      ∫ τ in (reweight D w).timeDom hI (tt 0) (tt 1) (tt 2),
        signedPhase (reweight D w) cfs cs L γ δ η x (E 0 - E 1) (tt 0) τ := by
    rw [← tsum_mul_left]
    exact tsum_congr fun x => by ring
  erw [h2]
  ring


/-- The output time box of `sumint`. -/
def outBox {d : ℕ} (D : SumintDatum d) : Set (Fin 3 → ℝ) :=
  {tt | (∀ c, (D.qOut c : ℝ) ≤ tt c ∧ tt c ≤ D.qOut c + 1) ∧ max (tt 1) (tt 2) < tt 0}

/-- The output momentum set of `sumint`. -/
def outSet {d : ℕ} (D : SumintDatum d) (L γ η : ℝ) : Set (Fin 4 → Mom d) :=
  {v | (∀ c, (∃ nv : Fin d → ℤ, v c = D.wBar + latticePoint L nv) ∧ ‖v c - D.centre c‖ ≤ 1) ∧
    v 0 - v 1 = v 3 - v 2 ∧ v 0 ≠ v 1 ∧ ‖v 0 - v 1‖ ≤ L ^ (-γ + η)}

/-- `maxPar`. -/
noncomputable def maxPar {d : ℕ} (D : SumintDatum d) : ℝ :=
  ⨆ v, jbr (d := 1) (WithLp.toLp 2 fun _ => D.param v)

/-- The right-hand side of `sumint`. -/
noncomputable def sumintRHS (P : WTParams) (D : SumintDatum P.d) : ℝ :=
  P.C₁ * maxPar D ^ (P.η ^ 6) * (P.C₁ * P.δ ^ (-(1 : ℝ) / 2)) ^ D.S.M *
    P.L ^ ((D.S.M : ℝ) * (P.d - P.γ) -
      P.η ^ 2 * ((Finset.univ.filter fun i => D.S.nor i = false).card + D.M₁) -
      P.η ^ 8 * D.M₀ + P.η ^ 7)

/-- The pointwise form of `SumintSignedDoubled`. -/
def SumintDoubledAt (A : ℝ) (P : WTParams) : Prop :=
  ∀ (D : SumintDatum P.d) (hI : 0 < D.S.I) (coreFirstSign coreSign : Fin D.S.I → ℤˣ),
    D.Admissible A P.L P.γ P.η P.D → D.S.M ≤ P.N 1 ^ 4 →
      XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
          (fun tt v => signedExpr D coreFirstSign coreSign hI P.L P.γ (2 * P.δ) P.η tt v) ≤
        ENNReal.ofReal (sumintRHS P D)

theorem sumintSignedDoubled_iff : SumintSignedDoubled ↔ WTPrefixA SumintDoubledAt := Iff.rfl

/-- **`sumint` for weights of arbitrary size.** -/
def ScaledSumintAt (A : ℝ) (P : WTParams) : Prop :=
  0 < P.L → ∀ (D : SumintDatum P.d) (hI : 0 < D.S.I) (cfs cs : Fin D.S.I → ℤˣ),
    (∀ (p : D.S.TVar → ℝ) (a b : D.S.VIdx → Mom P.d → ℂ), WeightBounds D P.L P.γ P.η a b →
      ({ D with param := p, wK := a, wL := b } : SumintDatum P.d).Admissible A P.L P.γ P.η P.D) →
    D.S.M ≤ P.N 1 ^ 4 →
    ∀ (w : Row D → Mom P.d → ℂ) (s : Row D → ℝ), (∀ ρ, 0 ≤ s ρ) → RowBounds D w s →
      XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
        (fun tt v => signedExpr (reweight D w) cfs cs hI P.L P.γ (2 * P.δ) P.η tt v) ≤
      ENNReal.ofReal (∏ ρ, (s ρ * P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
        ENNReal.ofReal (sumintRHS P D)


theorem scaledSumintAt_of {A : ℝ} {P : WTParams} (h : SumintDoubledAt A P) : ScaledSumintAt A P := by
  intro hL D hI cfs cs hAdm hM w s hs0 hS
  by_cases hz : ∃ ρ, s ρ = 0
  · -- a zero weight kills the expression
    obtain ⟨ρ₀, hρ₀⟩ := hz
    have hw0 : w ρ₀ = 0 := by
      cases ρ₀ with
      | inl v =>
        refine eq_zero_of_SNorm_eq_zero (Λ₁ := 30 * P.d) (Λ₂ := 30 * P.d) (le_antisymm ?_ bot_le)
        simpa [hρ₀] using hS.1 v
      | inr v =>
        refine eq_zero_of_SNorm_eq_zero (Λ₁ := 30 * P.d) (Λ₂ := 0) (le_antisymm ?_ bot_le)
        simpa [hρ₀] using hS.2 v
    have hprod : ∏ ρ, (s ρ * P.L ^ (weightExp P.d P.γ P.η * rowG D ρ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ ρ₀) (by simp [hρ₀])
    rw [hprod]
    simp only [ENNReal.ofReal_zero, zero_mul]
    have hz2 : (fun tt v => signedExpr (reweight D w) cfs cs hI P.L P.γ (2 * P.δ) P.η tt v) =
        fun _ _ => (0 : ℂ) := by
      funext tt v
      unfold signedExpr
      have : ∀ x : D.S.VIdx → (Fin P.d → ℤ),
          (∏ v', (reweight D w).wK v' ((reweight D w).kVec P.L x v v') *
            (reweight D w).wL v' ((reweight D w).ℓVec P.L x v v')) = 0 := by
        intro x
        cases ρ₀ with
        | inl v' => exact Finset.prod_eq_zero (Finset.mem_univ v') (by simp [reweight, hw0])
        | inr v' => exact Finset.prod_eq_zero (Finset.mem_univ v') (by simp [reweight, hw0])
      simp only [this, zero_mul, tsum_zero, mul_zero]
    rw [hz2]
    exact (XNorm00Restr_zero _ _ _).le
  · have hz' : ∀ ρ, s ρ ≠ 0 := fun ρ h0 => hz ⟨ρ, h0⟩
    have hpos : ∀ ρ, 0 < s ρ := fun ρ => lt_of_le_of_ne (hs0 ρ) (Ne.symm (hz' ρ))
    set nn : Row D → ℝ := fun ρ => s ρ * P.L ^ (weightExp P.d P.γ P.η * rowG D ρ) with hnn
    have hnpos : ∀ ρ, 0 < nn ρ := fun ρ => mul_pos (hpos ρ) (Real.rpow_pos_of_pos hL _)
    set w' : Row D → Mom P.d → ℂ := fun ρ k => ((nn ρ)⁻¹ : ℝ) * w ρ k with hw'
    have hwb : WeightBounds D P.L P.γ P.η (fun v => w' (Sum.inl v)) (fun v => w' (Sum.inr v)) := by
      have key : ∀ ρ (Λ₁ Λ₂ : ℕ), SNorm Λ₁ Λ₂ (w ρ) ≤ ENNReal.ofReal (s ρ) →
          SNorm Λ₁ Λ₂ (w' ρ) ≤ ENNReal.ofReal (P.L ^ (-weightExp P.d P.γ P.η * rowG D ρ)) := by
        intro ρ Λ₁ Λ₂ hb
        have h1 := SNorm_smul_le Λ₁ Λ₂ (((nn ρ)⁻¹ : ℝ) : ℂ) (w ρ)
        refine h1.trans ?_
        rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (hnpos ρ).le)]
        refine (mul_le_mul_right hb _).trans ?_
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 (hnpos ρ).le)]
        refine le_of_eq (congrArg ENNReal.ofReal ?_)
        rw [hnn]
        simp only
        rw [neg_mul, Real.rpow_neg hL.le]
        have hs' := hz' ρ
        have hX : P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hL _).ne'
        field_simp
      exact fun v => ⟨key (Sum.inl v) _ _ (hS.1 v), key (Sum.inr v) _ _ (hS.2 v)⟩
    have hAdm' := hAdm D.param (fun v => w' (Sum.inl v)) (fun v => w' (Sum.inr v)) hwb
    have key := h (reweight D w') hI cfs cs hAdm' hM
    have hww : w = fun ρ k => ((nn ρ : ℝ) : ℂ) * w' ρ k := by
      funext ρ k
      simp only [hw']
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (hnpos ρ).ne', Complex.ofReal_one, one_mul]
    have hscale : (fun tt v => signedExpr (reweight D w) cfs cs hI P.L P.γ (2 * P.δ) P.η tt v) =
        fun tt v => (((∏ ρ, nn ρ : ℝ)) : ℂ) *
          signedExpr (reweight D w') cfs cs hI P.L P.γ (2 * P.δ) P.η tt v := by
      funext tt v
      conv_lhs => rw [hww]
      rw [signedExpr_reweight_scale D (fun ρ => ((nn ρ : ℝ) : ℂ)) w' cfs cs hI P.L P.γ (2 * P.δ) P.η tt v,
        Complex.ofReal_prod]
    rw [hscale]
    refine (XNorm00Restr_const_mul_le _ _ _ _ _).trans ?_
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Finset.prod_nonneg fun ρ _ => (hnpos ρ).le)]
    exact mul_le_mul_right key _

end WaveTurbulence.VineEstS3.Eng
