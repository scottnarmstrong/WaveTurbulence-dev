/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ClockPhase
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Brackets
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ScaledSumint

/-! # The cost of a mode: parameters and output frequencies (engine step ASM)

For a mode tuple `m`, `⟨Δ_m(v)⟩ ≲ (√2)^{2|ρ|} ∏_ρ (2 ⟨m_ρ/2⟩)^2`, and likewise for the output frequency.  Hence the
`η⁶`-power of the maximal parameter of the shifted datum and the output modulation cost
are bounded by `C^{|ρ|} maxPar(D)^{η⁶} ∏_ρ ⟨m_ρ/2⟩^{θ}`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS Finset
open scoped ENNReal

variable {d : ℕ} (D : SumintPar.SumintDatum d)

/-- `⟨(m_ρ)/2⟩`, the bracket of a mode. -/
noncomputable def modeBr (m : Row D → Fin 2 → ℤ) (ρ : Row D) : ℝ := timeBracket (half (m ρ))

theorem one_le_modeBr (m : Row D → Fin 2 → ℤ) (ρ : Row D) : 1 ≤ modeBr D m ρ := one_le_timeBracket _

/-- `WaveTurbulence.VineEstS3.Eng.Jb (Δ_m v) ≤ (√2)^{2|Row|} ∏_ρ (2⟨m_ρ/2⟩)²`. -/
theorem Jb_modeParam_le (slot : Row D → Fin 2 → Slot D) (m : Row D → Fin 2 → ℤ) (v : D.S.TVar) :
    WaveTurbulence.VineEstS3.Eng.Jb (modeParam D slot m v) ≤
      Real.sqrt 2 ^ (2 * Fintype.card (Row D)) * ∏ ρ, (2 * modeBr D m ρ) ^ 2 := by
  classical
  unfold modeParam slotTotal
  have h1 : (∑ ρ, ∑ i, if slot ρ i = Sum.inl v then (m ρ i : ℝ) else 0) =
      ∑ p : Row D × Fin 2, if slot p.1 p.2 = Sum.inl v then (m p.1 p.2 : ℝ) else 0 :=
    (Fintype.sum_prod_type (fun p : Row D × Fin 2 => if slot p.1 p.2 = Sum.inl v then (m p.1 p.2 : ℝ) else 0)).symm
  rw [h1]
  refine (WaveTurbulence.VineEstS3.Eng.Jb_select_le (fun p : Row D × Fin 2 => slot p.1 p.2 = Sum.inl v) _).trans ?_
  rw [Fintype.card_prod, Fintype.card_fin, mul_comm (Fintype.card (Row D)) 2]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (Real.sqrt_nonneg _) _)
  rw [Fintype.prod_prod_type]
  have key : ∀ ρ : Row D, ∏ i : Fin 2, WaveTurbulence.VineEstS3.Eng.Jb (m ρ i : ℝ) ≤ (2 * modeBr D m ρ) ^ 2 := by
    intro ρ
    rw [Fin.prod_univ_two, sq]
    exact mul_le_mul (WaveTurbulence.VineEstS3.Eng.Jb_le_two_timeBracket (m ρ) 0) (WaveTurbulence.VineEstS3.Eng.Jb_le_two_timeBracket (m ρ) 1)
      (WaveTurbulence.VineEstS3.Eng.Jb_pos _).le (by have := one_le_modeBr D m ρ; linarith)
  exact Finset.prod_le_prod₀ (fun ρ _ => Finset.prod_nonneg fun i _ => (WaveTurbulence.VineEstS3.Eng.Jb_pos _).le) (fun ρ _ => key ρ)


theorem jbr_one_dim (t : ℝ) : jbr (d := 1) (WithLp.toLp 2 fun _ => t) = WaveTurbulence.VineEstS3.Eng.Jb t := by
  unfold jbr WaveTurbulence.VineEstS3.Eng.Jb
  congr 2
  rw [EuclideanSpace.norm_eq]
  simp [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Real.sqrt_sq_eq_abs, sq_abs]

theorem maxPar_eq (D' : SumintPar.SumintDatum d) : maxPar D' = ⨆ v, WaveTurbulence.VineEstS3.Eng.Jb (D'.param v) := by
  unfold maxPar
  exact iSup_congr fun v => jbr_one_dim _

theorem one_le_prod_real {ι : Type*} [Fintype ι] (f : ι → ℝ) (h : ∀ i, 1 ≤ f i) : 1 ≤ ∏ i, f i := by
  calc (1 : ℝ) = ∏ _i : ι, (1 : ℝ) := by simp
    _ ≤ ∏ i, f i := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun i _ => h i)

/-- The bracket of the output frequency. -/
theorem timeBracket_modeFreq_le (slot : Row D → Fin 2 → Slot D) (m : Row D → Fin 2 → ℤ) :
    timeBracket (fun c => modeFreq D slot m c / 2) ≤
      Real.sqrt 2 ^ (2 * Fintype.card (Row D)) * ∏ ρ, modeBr D m ρ ^ 2 := by
  classical
  have h2 : 1 ≤ ∏ ρ, modeBr D m ρ ^ 2 :=
    one_le_prod_real _ fun ρ => one_le_pow₀ (one_le_modeBr D m ρ)
  have ha : 1 ≤ Real.sqrt 2 ^ (2 * Fintype.card (Row D)) * ∏ ρ, modeBr D m ρ ^ 2 := by
    have h1 : 1 ≤ Real.sqrt 2 ^ (2 * Fintype.card (Row D)) :=
      one_le_pow₀ (by rw [Real.one_le_sqrt]; norm_num)
    nlinarith
  refine timeBracket_le ha fun c => ?_
  show WaveTurbulence.VineEstS3.Eng.Jb (modeFreq D slot m c / 2) ≤ _
  have h1 : modeFreq D slot m c / 2 =
      ∑ p : Row D × Fin 2, if slot p.1 p.2 = Sum.inr c then ((m p.1 p.2 : ℝ) / 2) else 0 := by
    unfold modeFreq slotTotal
    rw [Finset.sum_div, Fintype.sum_prod_type (f := fun p : Row D × Fin 2 =>
      if slot p.1 p.2 = Sum.inr c then ((m p.1 p.2 : ℝ) / 2) else 0)]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [h1]
  refine (WaveTurbulence.VineEstS3.Eng.Jb_select_le (fun p : Row D × Fin 2 => slot p.1 p.2 = Sum.inr c) _).trans ?_
  rw [Fintype.card_prod, Fintype.card_fin, mul_comm (Fintype.card (Row D)) 2]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (Real.sqrt_nonneg _) _)
  rw [Fintype.prod_prod_type]
  have key : ∀ ρ : Row D, ∏ i : Fin 2, WaveTurbulence.VineEstS3.Eng.Jb ((m ρ i : ℝ) / 2) ≤ modeBr D m ρ ^ 2 := by
    intro ρ
    rw [Fin.prod_univ_two, sq]
    exact mul_le_mul (WaveTurbulence.VineEstS3.Eng.Jb_half_le_timeBracket (m ρ) 0) (WaveTurbulence.VineEstS3.Eng.Jb_half_le_timeBracket (m ρ) 1)
      (WaveTurbulence.VineEstS3.Eng.Jb_pos _).le (by have := one_le_modeBr D m ρ; linarith)
  exact Finset.prod_le_prod₀ (fun ρ _ => Finset.prod_nonneg fun i _ => (WaveTurbulence.VineEstS3.Eng.Jb_pos _).le) (fun ρ _ => key ρ)

end WaveTurbulence.VineEstS3Par.Eng
