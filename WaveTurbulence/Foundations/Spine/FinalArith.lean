/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.KernelCore
/-! # The final arithmetic of the local ladder bound (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset

lemma prod_rungBudget {n : ℕ} (p : Fin n → Prop) [∀ k, Decidable (p k)] (d : ℕ) (γ x δ L C0 : ℝ) :
    ∏ k : Fin n, rungBudget d γ x δ L C0 (p k) =
      (C0 * (δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ))) ^ n *
        (L ^ (-x)) ^ (Finset.univ.filter p).card := by
  unfold rungBudget
  have h : ∀ k : Fin n, C0 * (δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ) * (if p k then L ^ (-x) else 1)) =
      (C0 * (δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ))) * (if p k then L ^ (-x) else 1) := fun k => by ring
  simp_rw [h]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

lemma card_code (n : ℕ) : Fintype.card (LadderDarts.Ctx.Code n) = 4 * n + 2 := by
  simp [LadderDarts.Ctx.Code, Fintype.card_sum, Fintype.card_prod]
  ring

lemma coupling_pow_alg (a δ C0 : ℝ) (n : ℕ) (ha : 0 < a) (hδ : 0 < δ) :
    (δ / (2 * a)) ^ (2 * n + 3) * (C0 * (δ⁻¹ * a ^ 2)) ^ n =
      δ ^ (n + 3) / 8 * (C0 / 4) ^ n * a⁻¹ ^ 3 := by
  have h1 : (δ / (2 * a)) ^ (2 * n + 3) = δ ^ (2 * n + 3) / (2 ^ (2 * n + 3) * a ^ (2 * n + 3)) := by
    rw [div_pow, mul_pow]
  have h2 : (C0 * (δ⁻¹ * a ^ 2)) ^ n = C0 ^ n * (δ ^ n)⁻¹ * (a ^ (2 * n)) := by
    rw [mul_pow, mul_pow, inv_pow, ← pow_mul]; ring
  rw [h1, h2, inv_pow]
  have h3 : (2 : ℝ) ^ (2 * n + 3) = 8 * 4 ^ n := by
    rw [pow_add, pow_mul]; norm_num; ring
  have h4 : δ ^ (2 * n + 3) = δ ^ (n + 3) * δ ^ n := by rw [← pow_add]; ring_nf
  rw [h3, h4, div_pow]
  have : (a ^ (2 * n + 3)) = a ^ (2 * n) * a ^ 3 := by rw [pow_add]
  rw [this]
  have hn : (a ^ (2 * n)) ≠ 0 := pow_ne_zero _ ha.ne'
  field_simp

lemma coupling_pow_mul {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (C0 : ℝ) (d : ℕ) (γ : ℝ) (n : ℕ) :
    (δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n + 3) *
      (C0 * (δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ))) ^ n =
    δ ^ (n + 3) / 8 * (C0 / 4) ^ n * (L ^ ((d : ℝ) - γ))⁻¹ ^ 3 := by
  have ha : 0 < L ^ ((d : ℝ) - γ) := Real.rpow_pos_of_pos hL _
  have hE : L ^ ((2 : ℝ) * d - 2 * γ) = (L ^ ((d : ℝ) - γ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]; congr 1; push_cast; ring
  rw [hE]
  exact coupling_pow_alg _ _ _ _ ha hδ

lemma final_bound {L δ x M C0 K γ NC : ℝ} {d n inc ndiff : ℕ} (hd : 3 ≤ d) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hL1 : 1 ≤ L) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hC0 : 0 ≤ C0) (hM : 0 ≤ M)
    (hinc : inc ≤ ndiff + 2) (hNC0 : 0 ≤ NC) (hNC : NC ≤ 2 * (3 * L) ^ (16 * d))
    (hK : K ≤ (δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n + 3) *
      (NC * (36 ^ n * (M ^ (4 * n + 2) *
        ((C0 * (δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ))) ^ n * (L ^ (-x)) ^ ndiff)))) ) :
    K ≤ (1 + 9 * M ^ 4 * C0 + 3 ^ (16 * d) * M ^ 2) *
      ((1 + 9 * M ^ 4 * C0 + 3 ^ (16 * d) * M ^ 2) * δ) ^ (n + 1) *
        L ^ (-x * (inc : ℝ) + 20 * (d : ℝ)) := by
  have hL0 : 0 < L := by linarith
  set C1 := 1 + 9 * M ^ 4 * C0 + 3 ^ (16 * d) * M ^ 2 with hC1
  have hC1' : 1 ≤ C1 := by
    have : 0 ≤ 9 * M ^ 4 * C0 := by positivity
    have : 0 ≤ 3 ^ (16 * d) * M ^ 2 := by positivity
    linarith
  have ha : 0 < L ^ ((d : ℝ) - γ) := Real.rpow_pos_of_pos hL0 _
  -- rewrite the coupling power
  have e1 := coupling_pow_mul (L := L) (δ := δ) hL0 hδ C0 d γ n
  have hK' : K ≤ (δ ^ (n + 3) / 8 * (C0 / 4) ^ n * (L ^ ((d : ℝ) - γ))⁻¹ ^ 3) *
      (NC * (36 ^ n * (M ^ (4 * n + 2) * (L ^ (-x)) ^ ndiff))) := by
    refine hK.trans (le_of_eq ?_)
    rw [← e1]; ring
  -- rpow forms
  have hA : (L ^ ((d : ℝ) - γ))⁻¹ ^ 3 = L ^ (-(3 * ((d : ℝ) - γ))) := by
    rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le, ← Real.rpow_neg hL0.le]
    congr 1; push_cast; ring
  have hLd : L ^ (16 * d) = L ^ ((16 * d : ℕ) : ℝ) := (Real.rpow_natCast L (16 * d)).symm
  have hNC' : NC ≤ 2 * 3 ^ (16 * d) * L ^ ((16 * d : ℕ) : ℝ) := by
    rw [← hLd]; rw [mul_pow] at hNC; linarith
  have hLx : (L ^ (-x)) ^ ndiff = L ^ (-x * (ndiff : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
  have hexp : L ^ (-(3 * ((d : ℝ) - γ))) * L ^ ((16 * d : ℕ) : ℝ) * L ^ (-x * (ndiff : ℝ)) ≤
      L ^ (-x * (inc : ℝ) + 20 * (d : ℝ)) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    have hinc' : (inc : ℝ) ≤ (ndiff : ℝ) + 2 := by exact_mod_cast hinc
    have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
    push_cast
    nlinarith
  set M2 := 3 ^ (16 * d) * M ^ 2 with hM2
  have hX : 0 ≤ L ^ (-(3 * ((d : ℝ) - γ))) := by positivity
  have hY : 0 ≤ L ^ ((16 * d : ℕ) : ℝ) := by positivity
  have hZ : 0 ≤ (L ^ (-x)) ^ ndiff := by positivity
  have hStep : K ≤ δ ^ (n + 3) * (9 * M ^ 4 * C0) ^ n * (M2 / 4) *
      (L ^ (-(3 * ((d : ℝ) - γ))) * L ^ ((16 * d : ℕ) : ℝ) * L ^ (-x * (ndiff : ℝ))) := by
    refine hK'.trans ?_
    rw [hA, hLx]
    have h36 : (36 : ℝ) ^ n * (C0 / 4) ^ n = (9 * C0) ^ n := by
      rw [← mul_pow]; congr 1; ring
    have hM4 : M ^ (4 * n + 2) = (M ^ 4) ^ n * M ^ 2 := by rw [pow_add, pow_mul]
    calc δ ^ (n + 3) / 8 * (C0 / 4) ^ n * L ^ (-(3 * ((d : ℝ) - γ))) *
          (NC * (36 ^ n * (M ^ (4 * n + 2) * L ^ (-x * (ndiff : ℝ)))))
        ≤ δ ^ (n + 3) / 8 * (C0 / 4) ^ n * L ^ (-(3 * ((d : ℝ) - γ))) *
          ((2 * 3 ^ (16 * d) * L ^ ((16 * d : ℕ) : ℝ)) *
            (36 ^ n * (M ^ (4 * n + 2) * L ^ (-x * (ndiff : ℝ))))) := by
          gcongr
      _ = δ ^ (n + 3) * (9 * M ^ 4 * C0) ^ n * (M2 / 4) *
          (L ^ (-(3 * ((d : ℝ) - γ))) * L ^ ((16 * d : ℕ) : ℝ) * L ^ (-x * (ndiff : ℝ))) := by
          rw [hM4, hM2, mul_pow, mul_pow]
          have : (36 : ℝ) ^ n = 36 ^ n := rfl
          calc _ = δ ^ (n + 3) * ((36 : ℝ) ^ n * (C0 / 4) ^ n) * (M ^ 4) ^ n * (3 ^ (16 * d) * M ^ 2 / 4) *
              (L ^ (-(3 * ((d : ℝ) - γ))) * L ^ ((16 * d : ℕ) : ℝ) * L ^ (-x * (ndiff : ℝ))) := by ring
            _ = _ := by rw [h36]; ring
  have hfin : δ ^ (n + 3) * (9 * M ^ 4 * C0) ^ n * (M2 / 4) *
      (L ^ (-(3 * ((d : ℝ) - γ))) * L ^ ((16 * d : ℕ) : ℝ) * L ^ (-x * (ndiff : ℝ))) ≤
      C1 * (C1 * δ) ^ (n + 1) * L ^ (-x * (inc : ℝ) + 20 * (d : ℝ)) := by
    have h1 : δ ^ (n + 3) ≤ δ ^ (n + 1) := pow_le_pow_of_le_one hδ.le hδ1 (by omega)
    have h2 : (9 * M ^ 4 * C0) ^ n ≤ C1 ^ n := by
      apply pow_le_pow_left₀ (by positivity); linarith [show 0 ≤ 3 ^ (16 * d) * M ^ 2 by positivity]
    have h3 : M2 / 4 ≤ C1 := by
      have : 0 ≤ 9 * M ^ 4 * C0 := by positivity
      have h4 : 0 ≤ M2 := by positivity
      linarith
    have h5 : C1 ^ n ≤ C1 ^ (n + 1) := pow_le_pow_right₀ hC1' (by omega)
    calc δ ^ (n + 3) * (9 * M ^ 4 * C0) ^ n * (M2 / 4) *
          (L ^ (-(3 * ((d : ℝ) - γ))) * L ^ ((16 * d : ℕ) : ℝ) * L ^ (-x * (ndiff : ℝ)))
        ≤ δ ^ (n + 1) * C1 ^ n * C1 * L ^ (-x * (inc : ℝ) + 20 * (d : ℝ)) := by
          gcongr
      _ ≤ δ ^ (n + 1) * C1 ^ (n + 1) * C1 * L ^ (-x * (inc : ℝ) + 20 * (d : ℝ)) := by
          gcongr
      _ = C1 * (C1 * δ) ^ (n + 1) * L ^ (-x * (inc : ℝ) + 20 * (d : ℝ)) := by
          rw [mul_pow]; ring
  exact hStep.trans hfin

end WaveTurbulence.LadderDecay
