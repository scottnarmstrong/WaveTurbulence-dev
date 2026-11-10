/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.NonregularCoupleP
public import WaveTurbulence.Foundations.Spine.StageOrderGrowth
public import WaveTurbulence.Foundations.CountLemmas.PowerAbsorption
/-! AMEND6' (design P*, F3): the numerical data of the garden and couple estimates. The garden threshold is of
log type, uniform in `2 <= m <= 10 R_{p+1}` and `N <= N_{p+1}^4` (it counts the `(d+1)^{4 m Lambda}` expansion
terms and the recursion loss `T^{8 m Lambda}`, `T` polynomial in `N + m`). -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Filter

theorem delta_pow_absorbP {C₁ δ ν : ℝ} (hC₁ : 0 ≤ C₁) (hδ0 : 0 < δ) (hX : 2 * C₁ * δ ^ (6 * ν) ≤ 1)
    (N : ℕ) : (2 * C₁) ^ N * δ ^ (6 * ν * (N : ℝ)) ≤ 1 := by
  rw [Real.rpow_mul_natCast hδ0.le, ← mul_pow]
  apply pow_le_one₀ _ hX
  have : 0 ≤ δ ^ (6 * ν) := Real.rpow_nonneg hδ0.le _
  positivity

theorem pow_le_rpow_of_pow_leP {M L : ℝ} (hM : 1 ≤ M) (hL : M ^ 140 ≤ L) {m : ℕ} (hm : 2 ≤ m) :
    M ^ m ≤ L ^ (((m : ℝ) - 1) / 70) := by
  have hL0 : 0 ≤ M ^ 140 := by positivity
  have h1 : (M ^ 140) ^ (((m : ℝ) - 1) / 70) ≤ L ^ (((m : ℝ) - 1) / 70) :=
    Real.rpow_le_rpow hL0 hL (by
      have : (2 : ℝ) ≤ m := by exact_mod_cast hm
      linarith)
  refine le_trans ?_ h1
  have hM0 : 0 ≤ M := by linarith
  have e : (M ^ 140) ^ (((m : ℝ) - 1) / 70) = M ^ (2 * ((m : ℝ) - 1)) := by
    rw [← Real.rpow_natCast M 140, ← Real.rpow_mul hM0]
    congr 1
    push_cast
    ring
  rw [e, ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le hM
  have : (2 : ℝ) ≤ m := by exact_mod_cast hm
  push_cast
  linarith

theorem gnum_aux {d Λ m N : ℕ} {C₁ δ ν η L : ℝ} (hm2 : 2 ≤ m) (T Tb : ℝ) (hT0 : 0 ≤ T) (hT : T ≤ Tb)
    (hZ1 : 1 ≤ ((d : ℝ) + 1) ^ (4 * Λ) * Tb ^ (8 * Λ) * (2 * C₁))
    (hZ : (((d : ℝ) + 1) ^ (4 * Λ) * Tb ^ (8 * Λ) * (2 * C₁)) ^ 140 ≤ L)
    (hC₁ : 1 ≤ C₁) (hδ0 : 0 < δ) (hδ : 2 * C₁ * δ ^ (6 * ν) ≤ 1) (hL1 : 1 ≤ L) (hη0 : 0 ≤ η) :
    ((d : ℝ) + 1) ^ (4 * m * Λ) * T ^ (8 * m * Λ) * (2 * C₁) ^ (N + m) * δ ^ (6 * ν * (N : ℝ)) *
      L ^ (-η ^ 7) * L ^ (-((m : ℝ) - 1) / 70) ≤ 1 := by
  set Z : ℝ := ((d : ℝ) + 1) ^ (4 * Λ) * Tb ^ (8 * Λ) * (2 * C₁) with hZdef
  have hL0 : 0 < L := by linarith
  have hd0 : (0 : ℝ) ≤ (d : ℝ) + 1 := by positivity
  have hTb0 : 0 ≤ Tb := hT0.trans hT
  have h1 : ((d : ℝ) + 1) ^ (4 * m * Λ) * T ^ (8 * m * Λ) * (2 * C₁) ^ (N + m) ≤
      Z ^ m * (2 * C₁) ^ N := by
    have e1 : ((d : ℝ) + 1) ^ (4 * m * Λ) = (((d : ℝ) + 1) ^ (4 * Λ)) ^ m := by rw [← pow_mul]; congr 1; ring
    have e2 : Tb ^ (8 * m * Λ) = (Tb ^ (8 * Λ)) ^ m := by rw [← pow_mul]; congr 1; ring
    have h2 : T ^ (8 * m * Λ) ≤ Tb ^ (8 * m * Λ) := pow_le_pow_left₀ hT0 hT _
    have hC0 : (0 : ℝ) ≤ 2 * C₁ := by linarith
    calc _ ≤ ((d : ℝ) + 1) ^ (4 * m * Λ) * Tb ^ (8 * m * Λ) * (2 * C₁) ^ (N + m) := by
          gcongr
      _ = Z ^ m * (2 * C₁) ^ N := by
          rw [hZdef, e1, e2, pow_add, mul_pow, mul_pow]
          ring
  have hZm := pow_le_rpow_of_pow_leP hZ1 hZ hm2
  have hLm : 0 < L ^ (((m : ℝ) - 1) / 70) := Real.rpow_pos_of_pos hL0 _
  have hneg : L ^ (-((m : ℝ) - 1) / 70) = (L ^ (((m : ℝ) - 1) / 70))⁻¹ := by
    rw [← Real.rpow_neg hL0.le]; congr 1; ring
  have hη : L ^ (-η ^ 7) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by
      have : 0 ≤ η ^ 7 := pow_nonneg hη0 7
      linarith)
  have habs := delta_pow_absorbP (by linarith : (0 : ℝ) ≤ C₁) hδ0 hδ N
  have hLn : 0 ≤ L ^ (-η ^ 7) := Real.rpow_nonneg hL0.le _
  have hZ0 : 0 ≤ Z ^ m := by positivity
  have hY : 0 ≤ (2 * C₁) ^ N * δ ^ (6 * ν * (N : ℝ)) := by
    have : 0 ≤ δ ^ (6 * ν * (N : ℝ)) := Real.rpow_nonneg hδ0.le _
    have : 0 ≤ (2 * C₁) ^ N := by positivity
    positivity
  calc _ ≤ Z ^ m * (2 * C₁) ^ N * δ ^ (6 * ν * (N : ℝ)) * L ^ (-η ^ 7) * L ^ (-((m : ℝ) - 1) / 70) := by
        gcongr
    _ = Z ^ m * ((2 * C₁) ^ N * δ ^ (6 * ν * (N : ℝ))) * L ^ (-η ^ 7) * (L ^ (((m : ℝ) - 1) / 70))⁻¹ := by
        rw [hneg]; ring
    _ ≤ Z ^ m * 1 * 1 * (L ^ (((m : ℝ) - 1) / 70))⁻¹ := by gcongr
    _ = Z ^ m / L ^ (((m : ℝ) - 1) / 70) := by ring
    _ ≤ 1 := (div_le_one hLm).mpr hZm


/-- The log exponent controlling every order and every number of roots in range. -/
@[expose] def logExp (P : WTParams) : ℕ := 4 * (40 * P.d) ^ (2 * P.D + 2)

theorem R_le_log_pow (P : WTParams) (hd : 1 ≤ P.d) (hlog : 1 ≤ Real.log P.L) (q : ℕ) :
    (P.R q : ℝ) ≤ Real.log P.L ^ logExp P := by
  unfold WTParams.R logExp
  refine (Rdown_le_log_pow P (P.D - q)).trans (pow_le_pow_right₀ hlog ?_)
  have h1 : (40 * P.d) ^ (2 * (P.D - q) + 1) ≤ (40 * P.d) ^ (2 * P.D + 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (40 * P.d) ^ (2 * P.D + 2) ≤ 4 * (40 * P.d) ^ (2 * P.D + 2) := by omega
  exact h1.trans h2

/-- The constant of the garden threshold. -/
@[expose] noncomputable def gardenC (P : WTParams) (Cφ : ℝ) (p : ℕ) : ℝ :=
  ((P.d : ℝ) + 1) ^ (4 * P.Lambda (p + 1)) *
    (1690 * ((2 * (P.d : ℝ)) ^ (40 * P.d) * 16 * max (Cφ + 1) P.C₁ * (P.Lambda (p + 1) : ℝ) / P.C₁)) ^
      (8 * P.Lambda (p + 1)) * (2 * P.C₁)

/-- The garden numerical data (the `hnum` of `garden_estimate_of_gate`), uniformly in the range. -/
@[expose] def GardenNum (P : WTParams) (Cφ : ℝ) (p : ℕ) : Prop :=
  ∀ m N : ℕ, 2 ≤ m → m ≤ 10 * P.R (p + 1) → N ≤ P.N (p + 1) ^ 4 →
    ((P.d : ℝ) + 1) ^ (4 * m * P.Lambda (p + 1)) * gardenT P Cφ p m N ^ (8 * m * P.Lambda (p + 1)) *
      (2 * P.C₁) ^ (N + m) * P.δ ^ (6 * P.ν * N) * P.L ^ (-P.η ^ 7) * P.L ^ (-((m : ℝ) - 1) / 70) ≤ 1

theorem gardenNum_of_numerics (P : WTParams) (Cφ : ℝ) (p : ℕ) (hd : 1 ≤ P.d) (hlog : 1 ≤ Real.log P.L)
    (hC₁ : 1 ≤ P.C₁) (hCφ : 0 ≤ Cφ) (hδ0 : 0 < P.δ) (hη0 : 0 ≤ P.η) (hL1 : 1 ≤ P.L)
    (hδ : 2 * P.C₁ * P.δ ^ (6 * P.ν) ≤ 1)
    (hE : gardenC P Cφ p * (1 + Real.log P.L) ^ (24 * logExp P * P.Lambda (p + 1)) ≤ P.L ^ ((1 : ℝ) / 140)) :
    GardenNum P Cφ p := by
  intro m N hm2 hmmax hN
  set ℓ : ℝ := Real.log P.L with hℓ
  set Λ := P.Lambda (p + 1) with hΛ
  set X := logExp P with hX
  have hL0 : 0 < P.L := by linarith
  have hℓ1 : 1 ≤ ℓ := hlog
  have hℓX : 1 ≤ ℓ ^ X := one_le_pow₀ hℓ1
  have hNl : (N : ℝ) ≤ ℓ ^ X := by
    have h1 : (N : ℝ) ≤ (P.N (p + 1) : ℝ) ^ 4 := by exact_mod_cast hN
    exact h1.trans (N_quartic_le_log_pow P hd hlog (p + 1))
  have hml : (m : ℝ) ≤ 10 * ℓ ^ X := by
    have h1 : (m : ℝ) ≤ 10 * (P.R (p + 1) : ℝ) := by exact_mod_cast hmmax
    exact h1.trans (by have := R_le_log_pow P hd hlog (p + 1); linarith)
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛ]; unfold WTParams.Lambda
    exact Nat.one_le_pow _ _ (by omega)
  have hΛR : (1 : ℝ) ≤ Λ := by exact_mod_cast hΛ1
  have hd1 : (1 : ℝ) ≤ P.d := by exact_mod_cast hd
  set mx : ℝ := max (Cφ + 1) P.C₁ with hmx
  have hmxC : P.C₁ ≤ mx := le_max_right _ _
  have hC0 : 0 < P.C₁ := by linarith
  set κ : ℝ := (2 * (P.d : ℝ)) ^ (40 * P.d) with hκ
  have hκ1 : 1 ≤ κ := one_le_pow₀ (by linarith)
  set c1 : ℝ := κ * 16 * mx * Λ / P.C₁ with hc1
  have hc1ge : 1 ≤ c1 := by
    rw [hc1, le_div_iff₀ hC0]
    have : P.C₁ ≤ κ * 16 * mx * Λ := by
      have h1 : 1 ≤ κ * 16 := by linarith
      have h2 : mx ≤ κ * 16 * mx := by nlinarith
      have h3 : κ * 16 * mx ≤ κ * 16 * mx * Λ := by nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ κ) (by norm_num : (0:ℝ) ≤ 16)) (by linarith : (0:ℝ) ≤ mx)]
      linarith
    linarith
  -- the bound on T
  have hT0 : 0 ≤ gardenT P Cφ p m N := by
    unfold gardenT
    have : 0 ≤ mx := by linarith
    positivity
  set Tb : ℝ := 1690 * c1 * ℓ ^ (3 * X) with hTb
  have hT : gardenT P Cφ p m N ≤ Tb := by
    unfold gardenT
    set a : ℕ := (N + m + 1) / 2 with ha
    have ha1 : (a : ℝ) ≤ ((N : ℝ) + m + 1) / 2 := by
      have : (a : ℝ) * 2 ≤ (N : ℝ) + m + 1 := by
        have : a * 2 ≤ N + m + 1 := by omega
        exact_mod_cast this
      linarith
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have hNm : (N : ℝ) + m + 2 ≤ 13 * ℓ ^ X := by linarith
    have hs0 : (0 : ℝ) ≤ (N : ℝ) + m + 2 := by positivity
    have h2a : 2 * (a : ℝ) + 1 ≤ 13 * ℓ ^ X := by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have haa : (a : ℝ) ≤ 13 * ℓ ^ X := by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have e : (2 * (a : ℝ) + 1) * a * κ * (2 * mx * (8 * (m : ℝ) * Λ)) / P.C₁ =
        ((2 * (a : ℝ) + 1) * a) * (m : ℝ) * c1 := by
      rw [hc1]; field_simp; ring
    rw [e]
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hc10 : 0 ≤ c1 := by linarith
    calc ((2 * (a : ℝ) + 1) * a) * (m : ℝ) * c1 ≤ ((13 * ℓ ^ X) * (13 * ℓ ^ X)) * (10 * ℓ ^ X) * c1 := by
          gcongr
      _ = Tb := by
          rw [hTb, show 3 * X = X + X + X by ring, pow_add, pow_add]; ring
  have hTb1 : 1 ≤ Tb := by
    rw [hTb]
    have : 1 ≤ ℓ ^ (3 * X) := one_le_pow₀ hℓ1
    nlinarith
  have hZ1 : 1 ≤ ((P.d : ℝ) + 1) ^ (4 * Λ) * Tb ^ (8 * Λ) * (2 * P.C₁) := by
    have h1 : 1 ≤ ((P.d : ℝ) + 1) ^ (4 * Λ) := one_le_pow₀ (by linarith)
    have h2 : 1 ≤ Tb ^ (8 * Λ) := one_le_pow₀ hTb1
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) (by linarith)
  have hZeq : ((P.d : ℝ) + 1) ^ (4 * Λ) * Tb ^ (8 * Λ) * (2 * P.C₁) =
      gardenC P Cφ p * ℓ ^ (24 * X * Λ) := by
    unfold gardenC
    rw [hTb, mul_pow, ← pow_mul]
    have e : 3 * X * (8 * Λ) = 24 * X * Λ := by ring
    rw [e]
    ring
  have hZle : ((P.d : ℝ) + 1) ^ (4 * Λ) * Tb ^ (8 * Λ) * (2 * P.C₁) ≤ P.L ^ ((1 : ℝ) / 140) := by
    rw [hZeq]
    refine le_trans ?_ hE
    have hg0 : 0 ≤ gardenC P Cφ p := by
      unfold gardenC
      have : 0 ≤ mx := by linarith
      positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) _) hg0
  have hZ140 : (((P.d : ℝ) + 1) ^ (4 * Λ) * Tb ^ (8 * Λ) * (2 * P.C₁)) ^ 140 ≤ P.L := by
    calc _ ≤ (P.L ^ ((1 : ℝ) / 140)) ^ 140 := pow_le_pow_left₀ (by linarith) hZle _
      _ = P.L := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  exact gnum_aux (d := P.d) (Λ := Λ) (m := m) (N := N) hm2 _ Tb hT0 hT hZ1 hZ140 hC₁ hδ0 hδ hL1 hη0


/-- The constant of the couple threshold. -/
@[expose] noncomputable def coupleC (P : WTParams) (Cφ : ℝ) (p : ℕ) : ℝ :=
  ((P.d : ℝ) + 1) ^ (2 * P.Lambda (p + 1)) *
    (16 * ((2 * (P.d : ℝ)) ^ (40 * P.d + 4 * P.Lambda (p + 1)) * 16 * max (Cφ + 1) P.C₁ *
      (P.Lambda (p + 1) : ℝ) / P.C₁)) ^ (8 * P.Lambda (p + 1)) * (2 * P.C₁)

/-- The couple numerical data (the `hnum` of `couple_estimate_of_gate`). -/
@[expose] def CoupleNum (P : WTParams) (Cφ : ℝ) (p : ℕ) : Prop :=
  ∀ N : ℕ, N ≤ P.N (p + 1) ^ 4 →
    ((P.d : ℝ) + 1) ^ (2 * P.Lambda (p + 1)) * coupleT P Cφ p N ^ (8 * P.Lambda (p + 1)) *
      (2 * P.C₁) ^ (N + 1) * P.δ ^ (6 * P.ν * N) * P.L ^ (-P.η ^ 7) ≤
      P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5))

theorem coupleNum_of_numerics (P : WTParams) (Cφ : ℝ) (p : ℕ) (hd : 1 ≤ P.d) (hlog : 1 ≤ Real.log P.L)
    (hC₁ : 1 ≤ P.C₁) (hCφ : 0 ≤ Cφ) (hδ0 : 0 < P.δ) (hL1 : 1 ≤ P.L)
    (hδ : 2 * P.C₁ * P.δ ^ (6 * P.ν) ≤ 1)
    (hE : coupleC P Cφ p * (1 + Real.log P.L) ^ (16 * logExp P * P.Lambda (p + 1)) ≤
      P.L ^ (P.η ^ 7 - (3 * P.theta (p + 1) + 2 * P.theta p) / 5)) :
    CoupleNum P Cφ p := by
  intro N hN
  set ℓ : ℝ := Real.log P.L with hℓ
  set Λ := P.Lambda (p + 1) with hΛ
  set X := logExp P with hX
  have hL0 : 0 < P.L := by linarith
  have hℓ1 : 1 ≤ ℓ := hlog
  have hℓX : 1 ≤ ℓ ^ X := one_le_pow₀ hℓ1
  have hNl : (N : ℝ) ≤ ℓ ^ X := by
    have h1 : (N : ℝ) ≤ (P.N (p + 1) : ℝ) ^ 4 := by exact_mod_cast hN
    exact h1.trans (N_quartic_le_log_pow P hd hlog (p + 1))
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛ]; unfold WTParams.Lambda
    exact Nat.one_le_pow _ _ (by omega)
  have hd1 : (1 : ℝ) ≤ P.d := by exact_mod_cast hd
  set mx : ℝ := max (Cφ + 1) P.C₁ with hmx
  have hmxC : P.C₁ ≤ mx := le_max_right _ _
  have hC0 : 0 < P.C₁ := by linarith
  set κ : ℝ := (2 * (P.d : ℝ)) ^ (40 * P.d + 4 * Λ) with hκ
  have hκ1 : 1 ≤ κ := one_le_pow₀ (by linarith)
  set c2 : ℝ := κ * 16 * mx * Λ / P.C₁ with hc2
  have hc2ge : 1 ≤ c2 := by
    rw [hc2, le_div_iff₀ hC0]
    have hΛR : (1 : ℝ) ≤ Λ := by exact_mod_cast hΛ1
    have h1 : 1 ≤ κ * 16 := by linarith
    have h2 : mx ≤ κ * 16 * mx := by nlinarith
    have h3 : κ * 16 * mx ≤ κ * 16 * mx * Λ := by nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ κ) (by norm_num : (0:ℝ) ≤ 16)) (by linarith : (0:ℝ) ≤ mx)]
    linarith
  have hT0 : 0 ≤ coupleT P Cφ p N := by
    unfold coupleT
    have : 0 ≤ mx := by linarith
    positivity
  set Tb : ℝ := 16 * c2 * ℓ ^ (2 * X) with hTb
  have hT : coupleT P Cφ p N ≤ Tb := by
    unfold coupleT
    set a : ℕ := (N + 2) / 2 with ha
    have ha1 : (a : ℝ) ≤ ((N : ℝ) + 2) / 2 := by
      have : (a : ℝ) * 2 ≤ (N : ℝ) + 2 := by
        have : a * 2 ≤ N + 2 := by omega
        exact_mod_cast this
      linarith
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have h2a : 2 * (a : ℝ) + 1 ≤ 4 * ℓ ^ X := by linarith
    have haa : (a : ℝ) ≤ 4 * ℓ ^ X := by linarith
    have e : (2 * (a : ℝ) + 1) * a * κ * (2 * mx * (8 * (Λ : ℝ))) / P.C₁ =
        ((2 * (a : ℝ) + 1) * a) * c2 := by
      rw [hc2]; field_simp; ring
    rw [e]
    have hc20 : 0 ≤ c2 := by linarith
    calc ((2 * (a : ℝ) + 1) * a) * c2 ≤ ((4 * ℓ ^ X) * (4 * ℓ ^ X)) * c2 := by gcongr
      _ = Tb := by
          rw [hTb, show 2 * X = X + X by ring, pow_add]; ring
  have hTb1 : 1 ≤ Tb := by
    rw [hTb]
    have : 1 ≤ ℓ ^ (2 * X) := one_le_pow₀ hℓ1
    nlinarith
  have hZeq : ((P.d : ℝ) + 1) ^ (2 * Λ) * Tb ^ (8 * Λ) * (2 * P.C₁) = coupleC P Cφ p * ℓ ^ (16 * X * Λ) := by
    unfold coupleC
    rw [hTb, mul_pow, ← pow_mul]
    have e : 2 * X * (8 * Λ) = 16 * X * Λ := by ring
    rw [e]
    ring
  have hZle : ((P.d : ℝ) + 1) ^ (2 * Λ) * Tb ^ (8 * Λ) * (2 * P.C₁) ≤
      P.L ^ (P.η ^ 7 - (3 * P.theta (p + 1) + 2 * P.theta p) / 5) := by
    rw [hZeq]
    refine le_trans ?_ hE
    have hg0 : 0 ≤ coupleC P Cφ p := by
      unfold coupleC
      have : 0 ≤ mx := by linarith
      positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) _) hg0
  have habs := delta_pow_absorbP (by linarith : (0 : ℝ) ≤ P.C₁) hδ0 hδ N
  have h1 : ((P.d : ℝ) + 1) ^ (2 * Λ) * coupleT P Cφ p N ^ (8 * Λ) * (2 * P.C₁) ^ (N + 1) ≤
      (((P.d : ℝ) + 1) ^ (2 * Λ) * Tb ^ (8 * Λ) * (2 * P.C₁)) * (2 * P.C₁) ^ N := by
    have h2 : coupleT P Cφ p N ^ (8 * Λ) ≤ Tb ^ (8 * Λ) := pow_le_pow_left₀ hT0 hT _
    calc _ ≤ ((P.d : ℝ) + 1) ^ (2 * Λ) * Tb ^ (8 * Λ) * (2 * P.C₁) ^ (N + 1) := by gcongr
      _ = _ := by rw [pow_succ]; ring
  have hLη : 0 < P.L ^ (-P.η ^ 7) := Real.rpow_pos_of_pos hL0 _
  have hY : 0 ≤ (2 * P.C₁) ^ N * P.δ ^ (6 * P.ν * (N : ℝ)) := by
    have : 0 ≤ P.δ ^ (6 * P.ν * (N : ℝ)) := Real.rpow_nonneg hδ0.le _
    positivity
  calc _ ≤ (((P.d : ℝ) + 1) ^ (2 * Λ) * Tb ^ (8 * Λ) * (2 * P.C₁)) * (2 * P.C₁) ^ N *
        P.δ ^ (6 * P.ν * (N : ℝ)) * P.L ^ (-P.η ^ 7) := by gcongr
    _ = (((P.d : ℝ) + 1) ^ (2 * Λ) * Tb ^ (8 * Λ) * (2 * P.C₁)) *
        ((2 * P.C₁) ^ N * P.δ ^ (6 * P.ν * (N : ℝ))) * P.L ^ (-P.η ^ 7) := by ring
    _ ≤ (((P.d : ℝ) + 1) ^ (2 * Λ) * Tb ^ (8 * Λ) * (2 * P.C₁)) * 1 * P.L ^ (-P.η ^ 7) := by gcongr
    _ ≤ P.L ^ (P.η ^ 7 - (3 * P.theta (p + 1) + 2 * P.theta p) / 5) * 1 * P.L ^ (-P.η ^ 7) := by gcongr
    _ = P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)) := by
        rw [mul_one, ← Real.rpow_add hL0]; congr 1; ring

end WaveTurbulence.LGSpine
