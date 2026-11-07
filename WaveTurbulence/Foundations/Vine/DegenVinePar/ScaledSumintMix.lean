/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.DegenVinePar.SumintMixDoubled
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ScaledSumint
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ClockedExpr
public import WaveTurbulence.Foundations.VineEst.VineEstS3.SNormAux
public import WaveTurbulence.Foundations.VineEst.VineEstS3.RestrScalar

/-! # `sumint` for weights of arbitrary size, with a character-mixture multiplier, parametric weights (V5 Step 4d)

Port of DEGEN-VINE `ScaledSumintMix` to `SumintPar.SumintDatum`: the `𝒦` weights may depend on `r = e - f`, the size
bounds are uniform in `r` and at the regularity `wN, wDec` of the datum.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.DegenVinePar
open WaveTurbulence.DegenVine
open WaveTurbulence WaveTurbulence.SumintPar WaveTurbulence.VineEstS3Par WaveTurbulence.VineEstS3Par.Eng
  WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS Finset MeasureTheory
open scoped ENNReal

theorem exprMix_reweight_scale {d : ℕ} (D : SumintPar.SumintDatum d) (n : Row D → ℂ)
    (w : Row D → Mom d → Mom d → ℂ) (M : CharMix D.S d) (hI : 0 < D.S.I) (L γ δ η : ℝ) (tt : Fin 3 → ℝ)
    (E : Fin 4 → Mom d) :
    exprMix (D := reweight D (fun ρ r k => n ρ * w ρ r k)) M hI L γ δ η tt E =
      (∏ ρ, n ρ) * exprMix (D := reweight D w) M hI L γ δ η tt E := by
  unfold exprMix
  have hp : ∀ x : D.S.VIdx → (Fin d → ℤ),
      (∏ v, (reweight D (fun ρ r k => n ρ * w ρ r k)).wK v (E 0 - E 1)
          ((reweight D (fun ρ r k => n ρ * w ρ r k)).kVec L x E v) *
        (reweight D (fun ρ r k => n ρ * w ρ r k)).wL v
          ((reweight D (fun ρ r k => n ρ * w ρ r k)).ℓVec L x E v)) =
      (∏ ρ, n ρ) * ∏ v, (reweight D w).wK v (E 0 - E 1) ((reweight D w).kVec L x E v) *
        (reweight D w).wL v ((reweight D w).ℓVec L x E v) := by
    intro x
    simp only [Fintype.prod_sum_type, Finset.prod_mul_distrib, reweight_kVec, reweight_ℓVec]
    ring
  simp only [hp]
  have h2 : (∑' x : D.S.VIdx → (Fin d → ℤ), (M.val L E x * ((∏ ρ, n ρ) * ∏ v, (reweight D w).wK v (E 0 - E 1) ((reweight D w).kVec L x E v) *
        (reweight D w).wL v ((reweight D w).ℓVec L x E v))) *
      ∫ τ in (reweight D w).timeDom hI (tt 0) (tt 1) (tt 2),
        (reweight D w).phase L γ δ η x (E 0 - E 1) (tt 0) τ) =
      (∏ ρ, n ρ) * ∑' x : D.S.VIdx → (Fin d → ℤ), (M.val L E x * ∏ v, (reweight D w).wK v (E 0 - E 1) ((reweight D w).kVec L x E v) *
        (reweight D w).wL v ((reweight D w).ℓVec L x E v)) *
      ∫ τ in (reweight D w).timeDom hI (tt 0) (tt 1) (tt 2),
        (reweight D w).phase L γ δ η x (E 0 - E 1) (tt 0) τ := by
    rw [← tsum_mul_left]
    exact tsum_congr fun x => by ring
  erw [h2]
  ring


/-- The pointwise form of `SumintMixParDoubled`. -/
def SumintMixParDoubledAt (A : ℝ) (P : WTParams) : Prop :=
  ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I), D.Admissible A P.L P.γ P.η P.D → D.S.M ≤ P.N 1 ^ 4 →
    ∀ M : CharMix D.S P.d,
      XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
          (fun tt v => exprMix M hI P.L P.γ (2 * P.δ) P.η tt v) ≤
        ENNReal.ofReal (M.mass * sumintRHS P D)

theorem sumintMixParDoubled_iff : SumintMixParDoubled ↔ WTPrefixA SumintMixParDoubledAt := Iff.rfl

/-- **`sumint` for weights of arbitrary size.** -/
def ScaledSumintMixAt (A : ℝ) (P : WTParams) : Prop :=
  0 < P.L → ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I) (M : CharMix D.S P.d),
    (∀ (p : D.S.TVar → ℝ) (a : D.S.VIdx → Mom P.d → Mom P.d → ℂ) (b : D.S.VIdx → Mom P.d → ℂ), WeightBounds D P.L P.γ P.η a b →
      ({ D with param := p, wK := a, wL := b } : SumintPar.SumintDatum P.d).Admissible A P.L P.γ P.η P.D) →
    D.S.M ≤ P.N 1 ^ 4 →
    ∀ (w : Row D → Mom P.d → Mom P.d → ℂ) (s : Row D → ℝ), (∀ ρ, 0 ≤ s ρ) → RowBounds D w s →
      XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
        (fun tt v => exprMix (D := reweight D w) M hI P.L P.γ (2 * P.δ) P.η tt v) ≤
      ENNReal.ofReal (∏ ρ, (s ρ * P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
        ENNReal.ofReal (M.mass * sumintRHS P D)


theorem scaledSumintMixAt_of {A : ℝ} {P : WTParams} (h : SumintMixParDoubledAt A P) : ScaledSumintMixAt A P := by
  intro hL D hI M hAdm hM w s hs0 hS
  by_cases hz : ∃ ρ, s ρ = 0
  · -- a zero weight kills the expression
    obtain ⟨ρ₀, hρ₀⟩ := hz
    have hw0 : (∃ v, ∀ r, w (Sum.inl v) r = 0) ∨ (∃ v, w (Sum.inr v) 0 = 0) := by
      cases ρ₀ with
      | inl v =>
        refine Or.inl ⟨v, fun r => VineEstS3.Eng.eq_zero_of_SNorm_eq_zero (Λ₁ := D.wN) (Λ₂ := D.wDec)
          (le_antisymm ?_ bot_le)⟩
        simpa [hρ₀] using hS.1 v r
      | inr v =>
        refine Or.inr ⟨v, VineEstS3.Eng.eq_zero_of_SNorm_eq_zero (Λ₁ := D.wN) (Λ₂ := 0) (le_antisymm ?_ bot_le)⟩
        simpa [hρ₀] using hS.2 v
    have hprod : ∏ ρ, (s ρ * P.L ^ (weightExp P.d P.γ P.η * rowG D ρ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ ρ₀) (by simp [hρ₀])
    rw [hprod]
    simp only [ENNReal.ofReal_zero, zero_mul]
    have hz2 : (fun tt v => exprMix (D := reweight D w) M hI P.L P.γ (2 * P.δ) P.η tt v) =
        fun _ _ => (0 : ℂ) := by
      funext tt v
      unfold exprMix
      have : ∀ x : D.S.VIdx → (Fin P.d → ℤ),
          (∏ v', (reweight D w).wK v' (v 0 - v 1) ((reweight D w).kVec P.L x v v') *
            (reweight D w).wL v' ((reweight D w).ℓVec P.L x v v')) = 0 := by
        intro x
        rcases hw0 with ⟨v', h0⟩ | ⟨v', h0⟩
        · exact Finset.prod_eq_zero (Finset.mem_univ v') (by simp [reweight, h0])
        · exact Finset.prod_eq_zero (Finset.mem_univ v') (by simp [reweight, h0])
      simp only [this, mul_zero, zero_mul, tsum_zero]
    rw [hz2]
    exact (VineEstS3.Eng.XNorm00Restr_zero _ _ _).le
  · have hz' : ∀ ρ, s ρ ≠ 0 := fun ρ h0 => hz ⟨ρ, h0⟩
    have hpos : ∀ ρ, 0 < s ρ := fun ρ => lt_of_le_of_ne (hs0 ρ) (Ne.symm (hz' ρ))
    set nn : Row D → ℝ := fun ρ => s ρ * P.L ^ (weightExp P.d P.γ P.η * rowG D ρ) with hnn
    have hnpos : ∀ ρ, 0 < nn ρ := fun ρ => mul_pos (hpos ρ) (Real.rpow_pos_of_pos hL _)
    set w' : Row D → Mom P.d → Mom P.d → ℂ := fun ρ r k => ((nn ρ)⁻¹ : ℝ) * w ρ r k with hw'
    have key : ∀ ρ (Λ₁ Λ₂ : ℕ) (r : Mom P.d), SNorm Λ₁ Λ₂ (w ρ r) ≤ ENNReal.ofReal (s ρ) →
        SNorm Λ₁ Λ₂ (w' ρ r) ≤ ENNReal.ofReal (P.L ^ (-weightExp P.d P.γ P.η * rowG D ρ)) := by
      intro ρ Λ₁ Λ₂ r hb
      have h1 := VineEstS3.Eng.SNorm_smul_le Λ₁ Λ₂ (((nn ρ)⁻¹ : ℝ) : ℂ) (w ρ r)
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
    have hwb : WeightBounds D P.L P.γ P.η (fun v => w' (Sum.inl v)) (fun v => w' (Sum.inr v) 0) :=
      fun v => ⟨fun r => key (Sum.inl v) _ _ r (hS.1 v r), key (Sum.inr v) _ _ 0 (hS.2 v)⟩
    have hAdm' := hAdm D.param (fun v => w' (Sum.inl v)) (fun v => w' (Sum.inr v) 0) hwb
    have key2 := h (reweight D w') hI hAdm' hM M
    have hww : w = fun ρ r k => ((nn ρ : ℝ) : ℂ) * w' ρ r k := by
      funext ρ r k
      simp only [hw']
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (hnpos ρ).ne', Complex.ofReal_one, one_mul]
    have hscale : (fun tt v => exprMix (D := reweight D w) M hI P.L P.γ (2 * P.δ) P.η tt v) =
        fun tt v => (((∏ ρ, nn ρ : ℝ)) : ℂ) *
          exprMix (D := reweight D w') M hI P.L P.γ (2 * P.δ) P.η tt v := by
      funext tt v
      conv_lhs => rw [hww]
      rw [exprMix_reweight_scale D (fun ρ => ((nn ρ : ℝ) : ℂ)) w' M hI P.L P.γ (2 * P.δ) P.η tt v,
        Complex.ofReal_prod]
    rw [hscale]
    refine (VineEstS3.Eng.XNorm00Restr_const_mul_le _ _ _ _ _).trans ?_
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Finset.prod_nonneg fun ρ _ => (hnpos ρ).le)]
    exact mul_le_mul_right key2 _

end WaveTurbulence.DegenVinePar
