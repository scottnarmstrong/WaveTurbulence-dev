/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkAsm.Assembly
public import WaveTurbulence.Foundations.Flower.MkAsm.Numeric

/-! # A5 MK-ASM: Core-F at fixed parameters, from the component bound and the conditional helper F. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs

namespace WaveTurbulence.Flower.MkAsm

/-- Absorption of the structure count and the `L`-exponents: `c · L^{B d (4Pm)} ≤ L^{100000 d Pm}`
when `c ≤ L^{4000 d Pm}` and `B ≤ 24000`. -/
theorem absorb_L {L B : ℝ} {d Pm : ℕ} (hL : 1 ≤ L) (hB : B ≤ 24000) {c : ℝ}
    (hc : c ≤ (L ^ (4000 * d)) ^ Pm) :
    c * L ^ (B * d * ((4 * Pm : ℕ) : ℝ)) ≤ L ^ (BcMK d * (Pm : ℝ)) := by
  have hL0 : 0 < L := by linarith
  have e1 : (L ^ (4000 * d)) ^ Pm = L ^ ((4000 * d * Pm : ℕ) : ℝ) := by
    rw [← pow_mul, ← Real.rpow_natCast]
  rw [e1] at hc
  calc c * L ^ (B * d * ((4 * Pm : ℕ) : ℝ))
      ≤ L ^ ((4000 * d * Pm : ℕ) : ℝ) * L ^ (B * d * ((4 * Pm : ℕ) : ℝ)) := by gcongr
    _ = L ^ (((4000 * d * Pm : ℕ) : ℝ) + B * d * ((4 * Pm : ℕ) : ℝ)) := (Real.rpow_add hL0 _ _).symm
    _ ≤ L ^ (BcMK d * (Pm : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hL
        unfold BcMK
        push_cast
        have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
        have hP : (0 : ℝ) ≤ Pm := Nat.cast_nonneg _
        nlinarith [mul_nonneg hd hP, mul_nonneg (mul_nonneg hd hP) (by linarith : (0 : ℝ) ≤ 24000 - B)]

theorem delta_mono {δ ν : ℝ} {N : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hν : 0 < ν) :
    δ ^ (7 * ν * (N : ℝ)) ≤ δ ^ (6 * ν * (N : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  nlinarith

/-- Core-F at fixed parameters. -/
theorem coreF_at {B : ℝ} (hB : B ≤ 24000) {Pm : ℕ} {P : WTParams}
    (hM : MarkedComponentBoundAtI B Pm P) (hcaps : CapsDecompFAt Pm P)
    (hν : 0 < P.ν) (hδ : 0 < P.δ) (hδ1 : P.δ ≤ 1) (hL : 1 ≤ P.L)
    (hthr : ∀ N p : ℕ, N ≤ P.N (p + 1) ^ 4 →
      ((4 * Pm : ℕ) : ℝ) ^ (4 * Pm) * ((N : ℝ) + 1) ^ (4 * Pm) * 2 ^ Pm ≤ (P.L ^ (4000 * P.d)) ^ Pm) :
    Fam.FlowerCoreFiltAt BcMK Pm P := by
  intro hγ p hp t ht s hs n n' ζ N hN kind pat dagger h b hb hh Rf σ hRf hdecay
  obtain ⟨Str, _, m, D, hcard, hR, hn, hv, heq⟩ :=
    hcaps (by linarith) hγ p hp t ht s hs n n' ζ N hN kind pat dagger h b hb hh Rf σ hRf hdecay
  rw [heq]
  have hL0 : 0 < P.L := by linarith
  have hgain : ∀ x c, (D x c).gain = 1 := by
    intro x c
    simp [CompData.gain, hv]
  have hb0 : 0 ≤ b := by linarith
  have hstruct : ∀ x, ‖∏ c, (D x c).val‖ ≤
      P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ)) * P.δ ^ (7 * P.ν * (N : ℝ)) * b ^ N := by
    intro x
    have := norm_prod_val_le hM hγ hp ht hs hb hL0 hδ (D x) (hR x) (hn x) hN
    simpa [hgain] using this
  have hsum : ‖∑ x, ∏ c, (D x c).val‖ ≤
      (Fintype.card Str : ℝ) * (P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ)) * P.δ ^ (7 * P.ν * (N : ℝ)) * b ^ N) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x, ‖∏ c, (D x c).val‖ ≤ ∑ _x : Str, (P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ)) *
          P.δ ^ (7 * P.ν * (N : ℝ)) * b ^ N) := Finset.sum_le_sum fun x _ => hstruct x
      _ = _ := by simp
  refine hsum.trans ?_
  have hcnt : (Fintype.card Str : ℝ) ≤ (P.L ^ (4000 * P.d)) ^ Pm := by
    refine hcard.trans ?_
    refine le_trans ?_ (hthr N p hN)
    have : (1 : ℝ) ≤ 2 ^ Pm := one_le_pow₀ (by norm_num)
    have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) N; linarith
    have hpow : ((N : ℝ) + 1) ^ (2 * Pm) ≤ ((N : ℝ) + 1) ^ (4 * Pm) := pow_le_pow_right₀ hN1 (by omega)
    have h4 : (0 : ℝ) ≤ ((4 * Pm : ℕ) : ℝ) ^ (4 * Pm) := by positivity
    have hnn : 0 ≤ ((4 * Pm : ℕ) : ℝ) ^ (4 * Pm) * ((N : ℝ) + 1) ^ (4 * Pm) := by positivity
    calc ((4 * Pm : ℕ) : ℝ) ^ (4 * Pm) * ((N : ℝ) + 1) ^ (2 * Pm)
        ≤ ((4 * Pm : ℕ) : ℝ) ^ (4 * Pm) * ((N : ℝ) + 1) ^ (4 * Pm) := mul_le_mul_of_nonneg_left hpow h4
      _ ≤ _ := by nlinarith
  have habs := absorb_L (d := P.d) (Pm := Pm) hL hB hcnt
  have hdel := delta_mono (N := N) hδ hδ1 hν
  have hbN : 0 ≤ b ^ N := by positivity
  have hLB : 0 ≤ P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ)) := by positivity
  have hδN : 0 ≤ P.δ ^ (7 * P.ν * (N : ℝ)) := by positivity
  calc (Fintype.card Str : ℝ) * (P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ)) * P.δ ^ (7 * P.ν * (N : ℝ)) * b ^ N)
      = ((Fintype.card Str : ℝ) * P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ))) * P.δ ^ (7 * P.ν * (N : ℝ)) * b ^ N := by ring
    _ ≤ P.L ^ (BcMK P.d * (Pm : ℝ)) * P.δ ^ (6 * P.ν * (N : ℝ)) * b ^ N := by
        have h1 : (Fintype.card Str : ℝ) * P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ)) ≤ P.L ^ (BcMK P.d * (Pm : ℝ)) :=
          habs
        gcongr

end WaveTurbulence.Flower.MkAsm
