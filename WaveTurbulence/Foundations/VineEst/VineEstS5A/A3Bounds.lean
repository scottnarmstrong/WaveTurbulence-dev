/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Clock
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ModeBounds2

/-! # The per-mode weight for arity-3 rows (V5 Step 4d-A, item 2)

Arity-3 version of `VineEstS3Par.Eng.mode_real_bound`: with three clocks per row the parameter and the output
frequency cost `∏_ρ ⟨m_ρ/2⟩³` (instead of `⟨m_ρ/2⟩²`); `θ = 6η⁶` still absorbs them for `η ≤ 1/2`
(`2·3·η⁸ + 3 η⁶ ≤ 6 η⁶`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS Finset
open scoped ENNReal

variable {d : ℕ} (D : SumintPar.SumintDatum d)

/-- `⟨(m_ρ)/2⟩`, the bracket of a mode. -/
noncomputable def modeBr3 (m : Row D → Fin 3 → ℤ) (ρ : Row D) : ℝ := timeBracket (half (m ρ))

theorem one_le_modeBr3 (m : Row D → Fin 3 → ℤ) (ρ : Row D) : 1 ≤ modeBr3 D m ρ := one_le_timeBracket _

theorem Jb_modeParam3_le (slot : Row D → Fin 3 → Slot D) (m : Row D → Fin 3 → ℤ) (v : D.S.TVar) :
    WaveTurbulence.VineEstS3.Eng.Jb (modeParam3 D slot m v) ≤
      Real.sqrt 2 ^ (3 * Fintype.card (Row D)) * ∏ ρ, (2 * modeBr3 D m ρ) ^ 3 := by
  classical
  unfold modeParam3 slotTotal3
  have h1 : (∑ ρ, ∑ i, if slot ρ i = Sum.inl v then (m ρ i : ℝ) else 0) =
      ∑ p : Row D × Fin 3, if slot p.1 p.2 = Sum.inl v then (m p.1 p.2 : ℝ) else 0 :=
    (Fintype.sum_prod_type (fun p : Row D × Fin 3 => if slot p.1 p.2 = Sum.inl v then (m p.1 p.2 : ℝ) else 0)).symm
  rw [h1]
  refine (WaveTurbulence.VineEstS3.Eng.Jb_select_le (fun p : Row D × Fin 3 => slot p.1 p.2 = Sum.inl v) _).trans ?_
  rw [Fintype.card_prod, Fintype.card_fin, mul_comm (Fintype.card (Row D)) 3]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (Real.sqrt_nonneg _) _)
  rw [Fintype.prod_prod_type]
  have key : ∀ ρ : Row D, ∏ i : Fin 3, WaveTurbulence.VineEstS3.Eng.Jb (m ρ i : ℝ) ≤ (2 * modeBr3 D m ρ) ^ 3 := by
    intro ρ
    rw [Fin.prod_univ_three, pow_succ, pow_succ, pow_one]
    have hb : 0 ≤ 2 * modeBr3 D m ρ := by have := one_le_modeBr3 D m ρ; linarith
    have e0 := WaveTurbulence.VineEstS3.Eng.Jb_le_two_timeBracket (m ρ) 0
    have e1 := WaveTurbulence.VineEstS3.Eng.Jb_le_two_timeBracket (m ρ) 1
    have e2 := WaveTurbulence.VineEstS3.Eng.Jb_le_two_timeBracket (m ρ) 2
    have p := WaveTurbulence.VineEstS3.Eng.Jb_pos
    exact mul_le_mul (mul_le_mul e0 e1 (p _).le hb) e2 (p _).le (mul_nonneg hb hb)
  exact Finset.prod_le_prod₀ (fun ρ _ => Finset.prod_nonneg fun i _ => (WaveTurbulence.VineEstS3.Eng.Jb_pos _).le) (fun ρ _ => key ρ)

/-- The bracket of the output frequency. -/
theorem timeBracket_modeFreq3_le (slot : Row D → Fin 3 → Slot D) (m : Row D → Fin 3 → ℤ) :
    timeBracket (fun c => modeFreq3 D slot m c / 2) ≤
      Real.sqrt 2 ^ (3 * Fintype.card (Row D)) * ∏ ρ, modeBr3 D m ρ ^ 3 := by
  classical
  have h2 : 1 ≤ ∏ ρ, modeBr3 D m ρ ^ 3 :=
    one_le_prod_real _ fun ρ => one_le_pow₀ (one_le_modeBr3 D m ρ)
  have ha : 1 ≤ Real.sqrt 2 ^ (3 * Fintype.card (Row D)) * ∏ ρ, modeBr3 D m ρ ^ 3 := by
    have h1 : 1 ≤ Real.sqrt 2 ^ (3 * Fintype.card (Row D)) :=
      one_le_pow₀ (by rw [Real.one_le_sqrt]; norm_num)
    nlinarith
  refine timeBracket_le ha fun c => ?_
  show WaveTurbulence.VineEstS3.Eng.Jb (modeFreq3 D slot m c / 2) ≤ _
  have h1 : modeFreq3 D slot m c / 2 =
      ∑ p : Row D × Fin 3, if slot p.1 p.2 = Sum.inr c then ((m p.1 p.2 : ℝ) / 2) else 0 := by
    unfold modeFreq3 slotTotal3
    rw [Finset.sum_div, Fintype.sum_prod_type (f := fun p : Row D × Fin 3 =>
      if slot p.1 p.2 = Sum.inr c then ((m p.1 p.2 : ℝ) / 2) else 0)]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [h1]
  refine (WaveTurbulence.VineEstS3.Eng.Jb_select_le (fun p : Row D × Fin 3 => slot p.1 p.2 = Sum.inr c) _).trans ?_
  rw [Fintype.card_prod, Fintype.card_fin, mul_comm (Fintype.card (Row D)) 3]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (Real.sqrt_nonneg _) _)
  rw [Fintype.prod_prod_type]
  have key : ∀ ρ : Row D, ∏ i : Fin 3, WaveTurbulence.VineEstS3.Eng.Jb ((m ρ i : ℝ) / 2) ≤ modeBr3 D m ρ ^ 3 := by
    intro ρ
    rw [Fin.prod_univ_three, pow_succ, pow_succ, pow_one]
    have hb : 0 ≤ modeBr3 D m ρ := by have := one_le_modeBr3 D m ρ; linarith
    have e0 := WaveTurbulence.VineEstS3.Eng.Jb_half_le_timeBracket (m ρ) 0
    have e1 := WaveTurbulence.VineEstS3.Eng.Jb_half_le_timeBracket (m ρ) 1
    have e2 := WaveTurbulence.VineEstS3.Eng.Jb_half_le_timeBracket (m ρ) 2
    have p := WaveTurbulence.VineEstS3.Eng.Jb_pos
    exact mul_le_mul (mul_le_mul e0 e1 (p _).le hb) e2 (p _).le (mul_nonneg hb hb)
  exact Finset.prod_le_prod₀ (fun ρ _ => Finset.prod_nonneg fun i _ => (WaveTurbulence.VineEstS3.Eng.Jb_pos _).le) (fun ρ _ => key ρ)

theorem maxPar_shift3_le (slot : Row D → Fin 3 → Slot D) (m : Row D → Fin 3 → ℤ) :
    maxPar { D with param := fun v => D.param v + modeParam3 D slot m v } ≤
      Real.sqrt 2 * maxPar D * (Real.sqrt 2 ^ (3 * Fintype.card (Row D)) *
        (8 ^ Fintype.card (Row D) * (∏ ρ, modeBr3 D m ρ) ^ 3)) := by
  rw [maxPar_eq, maxPar_eq]
  have hX : 0 ≤ Real.sqrt 2 * (⨆ v, WaveTurbulence.VineEstS3.Eng.Jb (D.param v)) * (Real.sqrt 2 ^ (3 * Fintype.card (Row D)) *
        (8 ^ Fintype.card (Row D) * (∏ ρ, modeBr3 D m ρ) ^ 3)) := by
    have h0 : 0 ≤ ⨆ v, WaveTurbulence.VineEstS3.Eng.Jb (D.param v) := Real.iSup_nonneg fun v => (WaveTurbulence.VineEstS3.Eng.Jb_pos _).le
    have hbr : 0 ≤ ∏ ρ, modeBr3 D m ρ := Finset.prod_nonneg fun ρ _ => (lt_of_lt_of_le zero_lt_one (one_le_modeBr3 D m ρ)).le
    positivity
  refine Real.iSup_le (fun v => ?_) hX
  have h1 := WaveTurbulence.VineEstS3.Eng.Jb_add_le (D.param v) (modeParam3 D slot m v)
  have h2 := Jb_modeParam3_le D slot m v
  have h3 : WaveTurbulence.VineEstS3.Eng.Jb (D.param v) ≤ ⨆ v, WaveTurbulence.VineEstS3.Eng.Jb (D.param v) := le_ciSup (f := fun v => WaveTurbulence.VineEstS3.Eng.Jb (D.param v)) (Finite.bddAbove_range _) v
  have h4 : ∏ ρ, (2 * modeBr3 D m ρ) ^ 3 = 8 ^ Fintype.card (Row D) * (∏ ρ, modeBr3 D m ρ) ^ 3 := by
    have : ∀ ρ : Row D, (2 * modeBr3 D m ρ) ^ 3 = 8 * modeBr3 D m ρ ^ 3 := fun ρ => by ring
    simp_rw [this]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow]
  rw [h4] at h2
  calc WaveTurbulence.VineEstS3.Eng.Jb (D.param v + modeParam3 D slot m v) ≤ Real.sqrt 2 * WaveTurbulence.VineEstS3.Eng.Jb (D.param v) * WaveTurbulence.VineEstS3.Eng.Jb (modeParam3 D slot m v) := h1
    _ ≤ Real.sqrt 2 * (⨆ v, WaveTurbulence.VineEstS3.Eng.Jb (D.param v)) * (Real.sqrt 2 ^ (3 * Fintype.card (Row D)) *
        (8 ^ Fintype.card (Row D) * (∏ ρ, modeBr3 D m ρ) ^ 3)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)) h2 (WaveTurbulence.VineEstS3.Eng.Jb_pos _).le
          (mul_nonneg (Real.sqrt_nonneg _) (le_trans (WaveTurbulence.VineEstS3.Eng.Jb_pos _).le h3))

/-- The `η`- and `|Row|`-dependent constant of the arity-3 per-mode weight. -/
noncomputable def engineConst3 (η : ℝ) (K : ℕ) : ℝ :=
  ((2 : ℝ) ^ (2 * η ^ 8) * Real.sqrt 2 ^ (η ^ 6)) *
    ((Real.sqrt 2 ^ 3) ^ (2 * η ^ 8) * (Real.sqrt 2 ^ 3) ^ (η ^ 6) * (8 : ℝ) ^ (η ^ 6)) ^ K

theorem engineConst3_nonneg (η : ℝ) (K : ℕ) : 0 ≤ engineConst3 η K := by
  unfold engineConst3; positivity

/-- **The per-mode weight (real form, arity 3).** -/
theorem mode_real_bound3 {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 2) (slot : Row D → Fin 3 → Slot D)
    (m : Row D → Fin 3 → ℤ) :
    (2 : ℝ) ^ (2 * η ^ 8) * (timeBracket fun c => modeFreq3 D slot m c / 2) ^ (2 * η ^ 8) *
        (maxPar { D with param := fun v => D.param v + modeParam3 D slot m v }) ^ (η ^ 6) ≤
      engineConst3 η (Fintype.card (Row D)) * (maxPar D) ^ (η ^ 6) * ∏ ρ, modeBr3 D m ρ ^ (6 * η ^ 6) := by
  set K := Fintype.card (Row D) with hK
  set X := ∏ ρ, modeBr3 D m ρ with hXdef
  set s : ℝ := Real.sqrt 2 ^ 3 with hs
  have hs0 : 0 < s := by positivity
  have hsK : Real.sqrt 2 ^ (3 * K) = s ^ K := by rw [hs, pow_mul]
  have hX1 : 1 ≤ X := one_le_prod_real _ fun ρ => one_le_modeBr3 D m ρ
  have hθa : 0 ≤ 2 * η ^ 8 := by positivity
  have hpp : 0 ≤ η ^ 6 := by positivity
  have hmP : 0 ≤ maxPar D := by rw [maxPar_eq]; exact Real.iSup_nonneg fun v => (WaveTurbulence.VineEstS3.Eng.Jb_pos _).le
  have h_tb : (timeBracket fun c => modeFreq3 D slot m c / 2) ≤ s ^ K * X ^ 3 := by
    have := timeBracket_modeFreq3_le D slot m
    rwa [hsK, Finset.prod_pow] at this
  have h_mp : maxPar { D with param := fun v => D.param v + modeParam3 D slot m v } ≤
      Real.sqrt 2 * maxPar D * (s ^ K * (8 ^ K * X ^ 3)) := by
    have := maxPar_shift3_le D slot m
    rwa [hsK] at this
  have hb0 : 0 ≤ timeBracket fun c => modeFreq3 D slot m c / 2 := (timeBracket_pos _).le
  have hP0 : 0 ≤ maxPar { D with param := fun v => D.param v + modeParam3 D slot m v } := by
    rw [maxPar_eq]; exact Real.iSup_nonneg fun v => (WaveTurbulence.VineEstS3.Eng.Jb_pos _).le
  have hX0 : 0 ≤ X := le_trans zero_le_one hX1
  have hsq : ∀ t : ℝ, (X ^ 3) ^ t = X ^ (3 * t) := by
    intro t
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0]
    norm_num
  have hA1 : (s ^ K * X ^ 3 : ℝ) ^ (2 * η ^ 8) = (s ^ (2 * η ^ 8)) ^ K * X ^ (3 * (2 * η ^ 8)) := by
    rw [Real.mul_rpow (by positivity) (by positivity), rpow_pow_comm hs0.le K (2 * η ^ 8), hsq]
  have hA2 : (Real.sqrt 2 * maxPar D * (s ^ K * (8 ^ K * X ^ 3)) : ℝ) ^ (η ^ 6) =
      Real.sqrt 2 ^ (η ^ 6) * maxPar D ^ (η ^ 6) *
        ((s ^ (η ^ 6)) ^ K * (((8 : ℝ) ^ (η ^ 6)) ^ K * X ^ (3 * η ^ 6))) := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hmP,
      Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      rpow_pow_comm hs0.le K (η ^ 6), rpow_pow_comm (x := 8) (by norm_num) K (η ^ 6), hsq]
  have hexp : X ^ (3 * (2 * η ^ 8)) * X ^ (3 * η ^ 6) ≤ X ^ (6 * η ^ 6) := by
    rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hX1)]
    refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
    have h2 : η ^ 2 ≤ 1 / 4 := by nlinarith
    have : η ^ 8 ≤ η ^ 6 / 4 := by
      have : η ^ 8 = η ^ 6 * η ^ 2 := by ring
      rw [this]; nlinarith [pow_nonneg hη0 6]
    nlinarith
  have hprodX : ∏ ρ, modeBr3 D m ρ ^ (6 * η ^ 6) = X ^ (6 * η ^ 6) := by
    rw [hXdef, Real.finsetProd_rpow]
    intro ρ _
    exact (lt_of_lt_of_le zero_lt_one (one_le_modeBr3 D m ρ)).le
  rw [hprodX]
  unfold engineConst3
  have hc : (s ^ (2 * η ^ 8) * s ^ (η ^ 6) * (8 : ℝ) ^ (η ^ 6)) ^ K =
      (s ^ (2 * η ^ 8)) ^ K * (s ^ (η ^ 6)) ^ K * ((8 : ℝ) ^ (η ^ 6)) ^ K := by
    rw [mul_pow, mul_pow]
  rw [← hs, hc]
  calc (2 : ℝ) ^ (2 * η ^ 8) * (timeBracket fun c => modeFreq3 D slot m c / 2) ^ (2 * η ^ 8) *
        (maxPar { D with param := fun v => D.param v + modeParam3 D slot m v }) ^ (η ^ 6)
      ≤ (2 : ℝ) ^ (2 * η ^ 8) * (s ^ K * X ^ 3 : ℝ) ^ (2 * η ^ 8) *
        (Real.sqrt 2 * maxPar D * (s ^ K * (8 ^ K * X ^ 3)) : ℝ) ^ (η ^ 6) := by
        gcongr
    _ = ((2 : ℝ) ^ (2 * η ^ 8) * Real.sqrt 2 ^ (η ^ 6)) *
          ((s ^ (2 * η ^ 8)) ^ K * (s ^ (η ^ 6)) ^ K * ((8 : ℝ) ^ (η ^ 6)) ^ K) *
          maxPar D ^ (η ^ 6) * (X ^ (3 * (2 * η ^ 8)) * X ^ (3 * η ^ 6)) := by
        rw [hA1, hA2]; ring
    _ ≤ _ := by
        gcongr

end WaveTurbulence.VineEstS3Par.Eng
