/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.Final4c
import Mathlib.Tactic

/-! # C4a PIN-FOURIER: the per-ladder arithmetic with removed rungs and segments

Main's `small_factor`/`arith_total` (TARGET L2038), adapted to o73 (18.5):
- `h` rungs of a ladder are removed from `X` (`m ≤ K + d + 1 + h`). This costs `Λ^{2h}`: the removed rungs' atoms
  are integrated as `Y` variables, each at cost `Λ = log L`.
- The retained rungs split into at most `h + 1` segments, each with its own factorial. This costs one more
  `exp(D_t Λ δ^{1+10ν}) ≤ Lam` per extra segment.

So a ladder costs main's bound times `(Lam Λ²)^h` (`small_factorMK`), and the whole garden costs main's bound
times `(Lam Λ²)^{∑ h}` (`arith_totalMK`). The base `128` becomes `256`, for the extra `2^{|Iv|}` of the floor
trick. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Flower.FinalMKPin
open WaveTurbulence.Ladder Finset

/-- Segmented factorials: one exponential per nonempty segment. -/
theorem prod_pow_div_fact_le {κ : Type*} [Fintype κ] [DecidableEq κ] {δ ν x : ℝ} (hδ : 0 < δ) (hx : 0 ≤ x)
    (Ks : κ → ℕ) :
    ∏ k, x ^ (Ks k) / (Nat.factorial (Ks k) : ℝ) ≤
      ((δ ^ (-1 / 2 - 5 * ν)) ^ 2) ^ (∑ k, Ks k) *
        Real.exp (x * δ ^ (1 + 10 * ν)) ^ (univ.filter fun k => Ks k ≠ 0).card := by
  have hE : 1 ≤ Real.exp (x * δ ^ (1 + 10 * ν)) := Real.one_le_exp (by positivity)
  have h1 : ∀ k, x ^ (Ks k) / (Nat.factorial (Ks k) : ℝ) ≤
      ((δ ^ (-1 / 2 - 5 * ν)) ^ 2) ^ (Ks k) * (if Ks k ≠ 0 then Real.exp (x * δ ^ (1 + 10 * ν)) else 1) := by
    intro k
    by_cases hk : Ks k = 0
    · simp [hk]
    · rw [if_pos hk]; exact pow_div_fact_le hδ hx (Ks k)
  calc ∏ k, x ^ (Ks k) / (Nat.factorial (Ks k) : ℝ)
      ≤ ∏ k, ((δ ^ (-1 / 2 - 5 * ν)) ^ 2) ^ (Ks k) * (if Ks k ≠ 0 then Real.exp (x * δ ^ (1 + 10 * ν)) else 1) :=
        Finset.prod_le_prod₀ (fun k _ => by positivity) (fun k _ => h1 k)
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← Finset.prod_filter, Finset.prod_const]

/-- **One small ladder** with `h` removed rungs and its retained rungs in segments. -/
theorem small_factorMK {κ : Type*} [Fintype κ] [DecidableEq κ] {δ ν Dt ρ X Y Λ a dR Lam C1 c1 c2 c3 e f : ℝ}
    {m d h : ℕ} (Ks : κ → ℕ)
    (hX : 1 ≤ X) (hΛ : 1 ≤ Λ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hν : 0 ≤ ν) (hDt : 0 ≤ Dt)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ f * a * X) (hY1 : 1 ≤ Y) (hY : Y ≤ c2 * dR * Λ) (ha : 1 ≤ a)
    (hdR : 1 ≤ dR) (hmK : m ≤ (∑ k, Ks k) + d + 1 + h) (hKm : (∑ k, Ks k) ≤ m)
    (hseg : (univ.filter fun k => Ks k ≠ 0).card ≤ h + 1)
    (hc1 : 0 < c1) (hc2 : 1 ≤ c2) (hc3 : 1 ≤ c3) (hef : e * f = c3) (he : 0 ≤ e) (_hf : 0 ≤ f)
    (hexp : Real.exp (Dt * δ ^ (1 + 10 * ν) * Λ) * Λ ^ (2 * d + 4) ≤ Lam)
    (hC : c1 * (c2 * dR) * (c3 * a) ≤ C1) :
    c1 ^ (2 * m + 2) * (∏ k, (e * ρ * Dt) ^ (Ks k) / (Nat.factorial (Ks k) : ℝ)) *
        Y ^ (2 * m + 2 - ∑ k, Ks k) ≤
      (C1 * δ ^ (-1 / 2 - 5 * ν)) ^ (2 * m + 2) * Lam * X ^ m * (Lam * Λ ^ 2) ^ h := by
  set K := ∑ k, Ks k with hKdef
  set Dl := δ ^ (-1 / 2 - 5 * ν) with hDl
  set E := Real.exp (Dt * Λ * δ ^ (1 + 10 * ν)) with hEdef
  have hDl1 : 1 ≤ Dl := one_le_Dl hδ hδ1 hν
  have hΛ0 : 0 < Λ := by linarith
  have hc2' : 1 ≤ c2 * dR := by nlinarith
  have hX0 : 0 ≤ X := by linarith
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hca : 1 ≤ c3 * a := by nlinarith
  have hLam : E * Λ ^ (2 * d + 4) ≤ Lam := by
    rw [hEdef, show Dt * Λ * δ ^ (1 + 10 * ν) = Dt * δ ^ (1 + 10 * ν) * Λ by ring]; exact hexp
  have hEL : E ≤ Lam := le_trans (le_mul_of_one_le_right (by linarith) (one_le_pow₀ hΛ)) hLam
  have hLam1 : 1 ≤ Lam := hE1.trans hEL
  -- the factorial products
  have e1 : (∏ k, (e * ρ * Dt) ^ (Ks k) / (Nat.factorial (Ks k) : ℝ)) ≤
      X ^ m * ∏ k, (c3 * a * Dt) ^ (Ks k) / (Nat.factorial (Ks k) : ℝ) := by
    calc (∏ k, (e * ρ * Dt) ^ (Ks k) / (Nat.factorial (Ks k) : ℝ))
        ≤ ∏ k, X ^ (Ks k) * ((c3 * a * Dt) ^ (Ks k) / (Nat.factorial (Ks k) : ℝ)) := by
          refine Finset.prod_le_prod₀ (fun k _ => by positivity) (fun k _ => ?_)
          rw [← mul_div_assoc, ← mul_pow]
          refine div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ _) (by positivity)
          calc e * ρ * Dt ≤ e * (f * a * X) * Dt := by gcongr
            _ = X * (c3 * a * Dt) := by rw [← hef]; ring
      _ = X ^ K * ∏ k, (c3 * a * Dt) ^ (Ks k) / (Nat.factorial (Ks k) : ℝ) := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      _ ≤ X ^ m * ∏ k, (c3 * a * Dt) ^ (Ks k) / (Nat.factorial (Ks k) : ℝ) := by
          gcongr
  have e2 : Y ^ (2 * m + 2 - K) ≤ (c2 * dR) ^ (2 * m + 2) * (Λ ^ K * (Λ ^ (2 * d + 4) * Λ ^ (2 * h))) := by
    calc Y ^ (2 * m + 2 - K) ≤ (c2 * dR * Λ) ^ (2 * m + 2 - K) := by gcongr
      _ = (c2 * dR) ^ (2 * m + 2 - K) * Λ ^ (2 * m + 2 - K) := mul_pow _ _ _
      _ ≤ (c2 * dR) ^ (2 * m + 2) * (Λ ^ K * (Λ ^ (2 * d + 4) * Λ ^ (2 * h))) := by
          apply mul_le_mul
          · exact pow_le_pow_right₀ hc2' (by omega)
          · rw [← pow_add, ← pow_add]; exact pow_le_pow_right₀ hΛ (by omega)
          · positivity
          · positivity
  have e3 : Λ ^ K * ∏ k, (c3 * a * Dt) ^ (Ks k) / (Nat.factorial (Ks k) : ℝ) ≤
      (c3 * a) ^ (2 * m + 2) * (Dl ^ (2 * m + 2) * E ^ (h + 1)) := by
    have hsplit : Λ ^ K * ∏ k, (c3 * a * Dt) ^ (Ks k) / (Nat.factorial (Ks k) : ℝ) =
        (c3 * a) ^ K * ∏ k, (Dt * Λ) ^ (Ks k) / (Nat.factorial (Ks k) : ℝ) := by
      rw [hKdef, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      simp only [mul_pow]; ring
    rw [hsplit]
    have hp := prod_pow_div_fact_le (ν := ν) hδ (by positivity : 0 ≤ Dt * Λ) Ks
    rw [← hEdef] at hp
    have hDl2 : (Dl ^ 2) ^ K ≤ Dl ^ (2 * m + 2) := by
      rw [← pow_mul]; exact pow_le_pow_right₀ hDl1 (by omega)
    have hEh : E ^ (univ.filter fun k => Ks k ≠ 0).card ≤ E ^ (h + 1) := pow_le_pow_right₀ hE1 hseg
    refine mul_le_mul (pow_le_pow_right₀ hca (by omega)) (hp.trans ?_) (by positivity) (by positivity)
    exact mul_le_mul hDl2 hEh (by positivity) (by positivity)
  have hC0 : 0 ≤ C1 := le_trans (mul_nonneg (mul_nonneg hc1.le (by linarith)) (by linarith)) hC
  calc c1 ^ (2 * m + 2) * (∏ k, (e * ρ * Dt) ^ (Ks k) / (Nat.factorial (Ks k) : ℝ)) * Y ^ (2 * m + 2 - K)
      ≤ c1 ^ (2 * m + 2) * (X ^ m * ∏ k, (c3 * a * Dt) ^ (Ks k) / (Nat.factorial (Ks k) : ℝ)) *
          ((c2 * dR) ^ (2 * m + 2) * (Λ ^ K * (Λ ^ (2 * d + 4) * Λ ^ (2 * h)))) := by
        gcongr
    _ = (c1 * (c2 * dR)) ^ (2 * m + 2) * X ^ m * (Λ ^ (2 * d + 4) * Λ ^ (2 * h)) *
          (Λ ^ K * ∏ k, (c3 * a * Dt) ^ (Ks k) / (Nat.factorial (Ks k) : ℝ)) := by
        rw [mul_pow c1]; ring
    _ ≤ (c1 * (c2 * dR)) ^ (2 * m + 2) * X ^ m * (Λ ^ (2 * d + 4) * Λ ^ (2 * h)) *
          ((c3 * a) ^ (2 * m + 2) * (Dl ^ (2 * m + 2) * E ^ (h + 1))) := by
        gcongr
    _ = (c1 * (c2 * dR) * (c3 * a)) ^ (2 * m + 2) * Dl ^ (2 * m + 2) * X ^ m *
          (E * Λ ^ (2 * d + 4)) * (E * Λ ^ 2) ^ h := by
        rw [mul_pow (c1 * (c2 * dR)), mul_pow E, pow_succ, ← pow_mul]; ring
    _ ≤ C1 ^ (2 * m + 2) * Dl ^ (2 * m + 2) * X ^ m * Lam * (Lam * Λ ^ 2) ^ h := by
        gcongr
    _ = _ := by rw [mul_pow C1 Dl]; ring

/-- **The product of the per-ladder estimates** (main's `arith_total` with removed rungs and segments). -/
theorem arith_totalMK {Q : Type} [Fintype Q] [DecidableEq Q] (m : Q → ℕ) (Ks : (S : Q) → Fin (m S + 1) → ℕ)
    (h : Q → ℕ) (small : Q → Prop) (X ρ : Q → ℝ) (nfree n d : ℕ) {δ ν Dt Y Λ a dR Lam C1 : ℝ}
    (hn : n = nfree + ∑ S, (2 * m S + 2))
    (hK : ∀ S, (∑ k, Ks S k) ≤ m S) (hKs : ∀ S, small S → m S ≤ (∑ k, Ks S k) + d + 1 + h S)
    (hK0 : ∀ S, ¬ small S → ∀ k, Ks S k = 0)
    (hseg : ∀ S, (univ.filter fun k => Ks S k ≠ 0).card ≤ h S + 1)
    (hX1 : ∀ S, small S → 1 ≤ X S) (hρ0 : ∀ S, 0 ≤ ρ S) (hρ : ∀ S, small S → ρ S ≤ 8 * a * X S)
    (hXL : ∀ S, ¬ small S → X S = Λ ^ 2)
    (hΛ : 1 ≤ Λ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hν : 0 ≤ ν) (hDt : 0 ≤ Dt)
    (hY1 : 1 ≤ Y) (hY : Y ≤ 180 * dR * Λ) (ha : 1 ≤ a) (hdR : 1 ≤ dR)
    (hexp : Real.exp (Dt * δ ^ (1 + 10 * ν) * Λ) * Λ ^ (2 * d + 4) ≤ Lam)
    (hΛLam : Λ ^ 2 ≤ Lam) (hfree : 256 * (180 * dR * Λ) ≤ Lam)
    (hC : 256 * (180 * dR) * (64 * a) ≤ C1) (hC1 : 1 ≤ C1) :
    (∏ S, ∏ k, (8 * ρ S * Dt) ^ (Ks S k) / (Nat.factorial (Ks S k) : ℝ)) * 256 ^ n *
        Y ^ (n - ∑ S, ∑ k, Ks S k) ≤
      (C1 * δ ^ (-1 / 2 - 5 * ν)) ^ n * Lam ^ (Fintype.card Q + nfree) * (∏ S, X S ^ (m S)) *
        (Lam * Λ ^ 2) ^ (∑ S, h S) := by
  set Dl := δ ^ (-1 / 2 - 5 * ν) with hDl
  set KS : Q → ℕ := fun S => ∑ k, Ks S k with hKS
  have hDl1 : 1 ≤ Dl := one_le_Dl hδ hδ1 hν
  have hLam1 : 1 ≤ Lam := by
    have : 1 ≤ Real.exp (Dt * δ ^ (1 + 10 * ν) * Λ) := Real.one_le_exp (by positivity)
    have h2 : 1 ≤ Λ ^ (2 * d + 4) := one_le_pow₀ hΛ
    nlinarith
  have hKN : ∀ S, KS S ≤ 2 * m S + 2 := fun S => by have := hK S; simp only [hKS]; omega
  have hmtot : n - ∑ S, KS S = nfree + ∑ S, (2 * m S + 2 - KS S) := by
    have : ∑ S, (2 * m S + 2 - KS S) = ∑ S, (2 * m S + 2) - ∑ S, KS S :=
      Finset.sum_tsub_distrib _ (fun S _ => hKN S)
    have hsumK : ∑ S, KS S ≤ ∑ S, (2 * m S + 2) := Finset.sum_le_sum (fun S _ => hKN S)
    omega
  have hLHS : (∏ S, ∏ k, (8 * ρ S * Dt) ^ (Ks S k) / (Nat.factorial (Ks S k) : ℝ)) * 256 ^ n *
      Y ^ (n - ∑ S, KS S) =
      (256 * Y) ^ nfree * ∏ S, (256 ^ (2 * m S + 2) *
        (∏ k, (8 * ρ S * Dt) ^ (Ks S k) / (Nat.factorial (Ks S k) : ℝ)) * Y ^ (2 * m S + 2 - KS S)) := by
    rw [hmtot, hn, pow_add, pow_add, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, mul_pow]
    ring
  have hRHS : (C1 * Dl) ^ n * Lam ^ (Fintype.card Q + nfree) * (∏ S, X S ^ (m S)) * (Lam * Λ ^ 2) ^ (∑ S, h S) =
      ((C1 * Dl) * Lam) ^ nfree * ∏ S, ((C1 * Dl) ^ (2 * m S + 2) * Lam * X S ^ (m S) * (Lam * Λ ^ 2) ^ (h S)) := by
    rw [hn, pow_add, pow_add, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, Finset.prod_const, Finset.card_univ, mul_pow]
    ring
  show (∏ S, ∏ k, (8 * ρ S * Dt) ^ (Ks S k) / (Nat.factorial (Ks S k) : ℝ)) * 256 ^ n *
      Y ^ (n - ∑ S, KS S) ≤ _
  rw [hLHS, hRHS]
  have hC0 : 0 ≤ C1 := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hnn : ∀ S, 0 ≤ 256 ^ (2 * m S + 2) * (∏ k, (8 * ρ S * Dt) ^ (Ks S k) / (Nat.factorial (Ks S k) : ℝ)) *
      Y ^ (2 * m S + 2 - KS S) := fun S => by
    have := hρ0 S
    exact mul_nonneg (mul_nonneg (by positivity) (Finset.prod_nonneg fun k _ => by positivity)) (by positivity)
  refine mul_le_mul ?_ ?_ (Finset.prod_nonneg (fun S _ => hnn S)) (by positivity)
  · apply pow_le_pow_left₀ (by positivity)
    calc 256 * Y ≤ 256 * (180 * dR * Λ) := by gcongr
      _ ≤ Lam := hfree
      _ = 1 * Lam := by ring
      _ ≤ (C1 * Dl) * Lam := by
          gcongr
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ C1 * Dl := by gcongr
  · refine Finset.prod_le_prod₀ (fun S _ => hnn S) (fun S _ => ?_)
    by_cases hs : small S
    · exact small_factorMK (c1 := 256) (c2 := 180) (c3 := 64) (e := 8) (f := 8) (Ks S) (hX1 S hs) hΛ hδ hδ1 hν
        hDt (hρ0 S) (hρ S hs) hY1 hY ha hdR (hKs S hs) (hK S) (hseg S) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) hexp (by simpa using hC)
    · have h0 : ∀ k, Ks S k = 0 := hK0 S hs
      have hK0' : KS S = 0 := by simp only [hKS, h0, Finset.sum_const_zero]
      rw [hK0', hXL S hs]
      simp only [h0, Nat.factorial_zero, Nat.cast_one, pow_zero, div_one, Finset.prod_const_one, mul_one,
        Nat.sub_zero]
      have hl := large_factor (m := m S) (c1 := 256) (c2 := 180) hΛ hδ hδ1 hν hY1 hY hdR (by norm_num)
        (by norm_num) hΛLam ((le_mul_of_one_le_right (by positivity) (by linarith)).trans hC)
      have h1 : 1 ≤ (Lam * Λ ^ 2) ^ (h S) := one_le_pow₀ (by nlinarith [one_le_pow₀ (n := 2) hΛ])
      calc (256 : ℝ) ^ (2 * m S + 2) * Y ^ (2 * m S + 2) ≤ (C1 * Dl) ^ (2 * m S + 2) * Lam * (Λ ^ 2) ^ m S := hl
        _ ≤ (C1 * Dl) ^ (2 * m S + 2) * Lam * (Λ ^ 2) ^ m S * (Lam * Λ ^ 2) ^ (h S) :=
            le_mul_of_one_le_right (by positivity) h1

/-- The class-bound constant against `256^n`. -/
theorem combine_realMK {c P Yv R0 C1 : ℝ} {n ι mY m' : ℕ} (hc : c ≤ 4 ^ n) (_hc0 : 0 ≤ c) (hP : 0 ≤ P)
    (hY1 : 1 ≤ Yv) (hι : ι ≤ n) (hm : mY ≤ m') (harith : P * 256 ^ n * Yv ^ m' ≤ R0) (hC1 : 1 ≤ C1)
    (hR0 : 0 ≤ R0) :
    c * 16 ^ ι * (P * Real.pi ^ ι * Yv ^ mY) ≤ C1 * R0 := by
  have hπ : Real.pi ^ ι ≤ 4 ^ n :=
    (pow_le_pow_left₀ Real.pi_pos.le Real.pi_le_four ι).trans (pow_le_pow_right₀ (by norm_num) hι)
  have h16 : (16 : ℝ) ^ ι ≤ 16 ^ n := pow_le_pow_right₀ (by norm_num) hι
  have hYm : Yv ^ mY ≤ Yv ^ m' := pow_le_pow_right₀ hY1 hm
  have h1 : c * 16 ^ ι * (P * Real.pi ^ ι * Yv ^ mY) ≤ 4 ^ n * 16 ^ n * (P * 4 ^ n * Yv ^ m') := by
    gcongr
  have h2 : (4 : ℝ) ^ n * 16 ^ n * (P * 4 ^ n * Yv ^ m') = P * 256 ^ n * Yv ^ m' := by
    have : (256 : ℝ) ^ n = 4 ^ n * 16 ^ n * 4 ^ n := by rw [← mul_pow, ← mul_pow]; norm_num
    rw [this]; ring
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ R0 := harith
    _ ≤ C1 * R0 := le_mul_of_one_le_left hR0 hC1

end WaveTurbulence.Flower.FinalMKPin
