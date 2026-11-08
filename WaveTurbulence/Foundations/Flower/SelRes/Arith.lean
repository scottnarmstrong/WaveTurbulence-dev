/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-! # D7 SEL-RES / Arith: real inequalities for the three regimes of the selected bound

With `c = 49d − 35`, `μ = δL^{2γ}`, `λ = πμM₂/4`:
- normal regime (`M₂ > L^{18c}`, `μ ≥ 4L^{−18c}`): `atom_low_normal`, `atom_high_normal`;
- tiny regime (`μ < 4L^{−18c}`): `atom_low_tiny`, `atom_high_tiny`, `atom_tiny_small` (ratios against `32δ^{−1/18}`)
  and `tiny_core` (the trivial bound beats `(δ^{10ν}/L)^{ord}` once `δ ≤ L^{−(12d+14)}`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.SelRes

/-! ### Real arithmetic for the three regimes (`c = 49d − 35`) -/

/-- Normal regime, low atom: `2 · (12/λ) · L^{22d+16} ≤ L^{71d−14} M^{−1/18}` with `λ = πμM/4`. -/
theorem atom_low_normal {L M μ d : ℝ} (hL : 2 ≤ L) (hd : 1 ≤ d) (hμ : 4 * L ^ (-(18 * (49 * d - 35))) ≤ μ)
    (hM : L ^ (18 * (49 * d - 35)) < M) :
    2 * (12 / (Real.pi * (μ * M) / 4)) * L ^ (22 * d + 16) ≤ L ^ (71 * d - 14) * M ^ (-(1 / 18 : ℝ)) := by
  set c := 49 * d - 35 with hc
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hLc : 0 < L ^ (18 * c) := Real.rpow_pos_of_pos hL0 _
  have hM0 : 0 < M := lt_trans hLc hM
  have hμ0 : 0 < μ := lt_of_lt_of_le (by positivity) hμ
  -- μ M^{17/18} ≥ 4 L^{−c}
  have hM17 : L ^ (17 * c) ≤ M ^ (17 / 18 : ℝ) := by
    have : L ^ (17 * c) = (L ^ (18 * c)) ^ (17 / 18 : ℝ) := by
      rw [← Real.rpow_mul hL0.le]; ring_nf
    rw [this]; exact Real.rpow_le_rpow hLc.le hM.le (by norm_num)
  have hkey : 4 * L ^ (-c) ≤ μ * M ^ (17 / 18 : ℝ) := by
    calc 4 * L ^ (-c) = 4 * L ^ (-(18 * c)) * L ^ (17 * c) := by
          rw [mul_assoc, ← Real.rpow_add hL0]; ring_nf
      _ ≤ μ * M ^ (17 / 18 : ℝ) := mul_le_mul hμ hM17 (Real.rpow_nonneg hL0.le _) hμ0.le
  have hMsplit : M = M ^ (17 / 18 : ℝ) * M ^ (1 / 18 : ℝ) := by
    rw [← Real.rpow_add hM0]; norm_num
  have hMinv : M ^ (-(1 / 18 : ℝ)) * M ^ (1 / 18 : ℝ) = 1 := by
    rw [← Real.rpow_add hM0]; norm_num
  have hM18 : 0 < M ^ (1 / 18 : ℝ) := Real.rpow_pos_of_pos hM0 _
  have hL5 : 24 / Real.pi ≤ L ^ (5 : ℝ) := by
    have h1 : (2 : ℝ) ^ (5 : ℝ) ≤ L ^ (5 : ℝ) := Real.rpow_le_rpow (by norm_num) hL (by norm_num)
    have h2 : 24 / Real.pi ≤ 32 := by
      rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
    have h3 : (2 : ℝ) ^ (5 : ℝ) = 32 := by norm_num
    linarith
  -- assemble
  have hlhs : 2 * (12 / (Real.pi * (μ * M) / 4)) * L ^ (22 * d + 16) =
      (96 / Real.pi) / (μ * M ^ (17 / 18 : ℝ)) * M ^ (-(1 / 18 : ℝ)) * L ^ (22 * d + 16) := by
    have hMm : M ^ (-(1 / 18 : ℝ)) = (M ^ (1 / 18 : ℝ))⁻¹ := by
      rw [Real.rpow_neg hM0.le]
    rw [hMm]
    conv_lhs => rw [hMsplit]
    field_simp
    norm_num
  rw [hlhs]
  have hb : (96 / Real.pi) / (μ * M ^ (17 / 18 : ℝ)) ≤ (24 / Real.pi) * L ^ c := by
    rw [div_le_iff₀ (by positivity)]
    have : (96 / Real.pi) = (24 / Real.pi) * L ^ c * (4 * L ^ (-c)) := by
      rw [show (24 / Real.pi) * L ^ c * (4 * L ^ (-c)) = (96 / Real.pi) * (L ^ c * L ^ (-c)) by ring,
        ← Real.rpow_add hL0, add_neg_cancel, Real.rpow_zero, mul_one]
    rw [this]
    exact mul_le_mul_of_nonneg_left hkey (by positivity)
  calc (96 / Real.pi) / (μ * M ^ (17 / 18 : ℝ)) * M ^ (-(1 / 18 : ℝ)) * L ^ (22 * d + 16)
      ≤ (24 / Real.pi) * L ^ c * M ^ (-(1 / 18 : ℝ)) * L ^ (22 * d + 16) := by
        gcongr
    _ = (24 / Real.pi) * L ^ (c + (22 * d + 16)) * M ^ (-(1 / 18 : ℝ)) := by
        rw [Real.rpow_add hL0 c (22 * d + 16)]; ring
    _ ≤ L ^ (5 : ℝ) * L ^ (c + (22 * d + 16)) * M ^ (-(1 / 18 : ℝ)) := by
        gcongr
    _ = L ^ (71 * d - 14) * M ^ (-(1 / 18 : ℝ)) := by
        rw [← Real.rpow_add hL0, hc]; ring_nf

/-- Normal regime, high atom: `2 L^{22d+16} ≤ L^{71d−14} M^{−1/18} (1+|ξ|)^{1/18}` when `|ξ| ≥ μM/4`. -/
theorem atom_high_normal {L M μ d ξ : ℝ} (hL : 2 ≤ L) (_hd : 1 ≤ d)
    (hμ : 4 * L ^ (-(18 * (49 * d - 35))) ≤ μ) (hM : 0 < M) (hξ : μ * M / 4 ≤ |ξ|) :
    2 * L ^ (22 * d + 16) ≤ L ^ (71 * d - 14) * M ^ (-(1 / 18 : ℝ)) * (1 + |ξ|) ^ (1 / 18 : ℝ) := by
  set c := 49 * d - 35 with hc
  have hL0 : 0 < L := by linarith
  have hμ0 : 0 < μ := lt_of_lt_of_le (by positivity) hμ
  have h1 : (μ / 4) ^ (1 / 18 : ℝ) * M ^ (1 / 18 : ℝ) ≤ (1 + |ξ|) ^ (1 / 18 : ℝ) := by
    rw [← Real.mul_rpow (by positivity) hM.le]
    exact Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg ξ]) (by norm_num)
  have h2 : L ^ (-c) ≤ (μ / 4) ^ (1 / 18 : ℝ) := by
    have : L ^ (-c) = (L ^ (-(18 * c))) ^ (1 / 18 : ℝ) := by rw [← Real.rpow_mul hL0.le]; ring_nf
    rw [this]; exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have hMinv : M ^ (-(1 / 18 : ℝ)) * M ^ (1 / 18 : ℝ) = 1 := by rw [← Real.rpow_add hM]; norm_num
  have hL5 : (2 : ℝ) ≤ L ^ (5 : ℝ) := by
    have : (2 : ℝ) ^ (5 : ℝ) ≤ L ^ (5 : ℝ) := Real.rpow_le_rpow (by norm_num) hL (by norm_num)
    have h3 : (2 : ℝ) ^ (5 : ℝ) = 32 := by norm_num
    linarith
  calc 2 * L ^ (22 * d + 16) ≤ L ^ (5 : ℝ) * L ^ (22 * d + 16) := by gcongr
    _ = L ^ (71 * d - 14) * L ^ (-c) := by rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, hc]; ring_nf
    _ ≤ L ^ (71 * d - 14) * (μ / 4) ^ (1 / 18 : ℝ) := by gcongr
    _ = L ^ (71 * d - 14) * M ^ (-(1 / 18 : ℝ)) * ((μ / 4) ^ (1 / 18 : ℝ) * M ^ (1 / 18 : ℝ)) := by
        rw [show L ^ (71 * d - 14) * M ^ (-(1 / 18 : ℝ)) * ((μ / 4) ^ (1 / 18 : ℝ) * M ^ (1 / 18 : ℝ)) =
          L ^ (71 * d - 14) * (μ / 4) ^ (1 / 18 : ℝ) * (M ^ (-(1 / 18 : ℝ)) * M ^ (1 / 18 : ℝ)) by ring, hMinv,
          mul_one]
    _ ≤ L ^ (71 * d - 14) * M ^ (-(1 / 18 : ℝ)) * (1 + |ξ|) ^ (1 / 18 : ℝ) := by gcongr

end WaveTurbulence.Flower.SelRes

namespace WaveTurbulence.Flower.SelRes

/-- Tiny regime, low atom (`μM ≥ 2`, `μ ≥ δ`): `2 · (12/λ) ≤ M^{−1/18} · 32 δ^{−1/18}`. -/
theorem atom_low_tiny {M μ δ : ℝ} (hδ : 0 < δ) (hμδ : δ ≤ μ) (hμM : 2 ≤ μ * M) :
    2 * (12 / (Real.pi * (μ * M) / 4)) ≤ M ^ (-(1 / 18 : ℝ)) * (32 * δ ^ (-(1 / 18 : ℝ))) := by
  have hμ : 0 < μ := lt_of_lt_of_le hδ hμδ
  have hM : 0 < M := by
    by_contra h; push Not at h; nlinarith
  have hμM0 : 0 < μ * M := by positivity
  have e1 : 2 * (12 / (Real.pi * (μ * M) / 4)) = (96 / Real.pi) * (μ * M)⁻¹ := by
    field_simp; norm_num
  rw [e1]
  have h1 : (μ * M)⁻¹ = (μ * M) ^ (-(17 / 18 : ℝ)) * μ ^ (-(1 / 18 : ℝ)) * M ^ (-(1 / 18 : ℝ)) := by
    rw [mul_assoc, ← Real.mul_rpow hμ.le hM.le, ← Real.rpow_add hμM0]
    norm_num
    rw [Real.rpow_neg_one, mul_inv]; ring
  rw [h1]
  have h2 : (μ * M) ^ (-(17 / 18 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have h3 : μ ^ (-(1 / 18 : ℝ)) ≤ δ ^ (-(1 / 18 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hδ hμδ (by norm_num)
  have h4 : 96 / Real.pi ≤ 32 := by rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
  have hp1 : 0 ≤ (μ * M) ^ (-(17 / 18 : ℝ)) := Real.rpow_nonneg hμM0.le _
  have hp2 : 0 ≤ μ ^ (-(1 / 18 : ℝ)) := Real.rpow_nonneg hμ.le _
  have hp3 : 0 ≤ M ^ (-(1 / 18 : ℝ)) := Real.rpow_nonneg hM.le _
  have hp4 : 0 ≤ δ ^ (-(1 / 18 : ℝ)) := Real.rpow_nonneg hδ.le _
  calc 96 / Real.pi * ((μ * M) ^ (-(17 / 18 : ℝ)) * μ ^ (-(1 / 18 : ℝ)) * M ^ (-(1 / 18 : ℝ)))
      ≤ 32 * (1 * δ ^ (-(1 / 18 : ℝ)) * M ^ (-(1 / 18 : ℝ))) := by gcongr
    _ = M ^ (-(1 / 18 : ℝ)) * (32 * δ ^ (-(1 / 18 : ℝ))) := by ring

/-- Tiny regime, high atom (`|ξ| ≥ μM/4`, `μ ≥ δ`): `2 ≤ M^{−1/18} (1+|ξ|)^{1/18} · 32 δ^{−1/18}`. -/
theorem atom_high_tiny {M μ δ ξ : ℝ} (hδ : 0 < δ) (hμδ : δ ≤ μ) (hM : 0 < M) (hξ : μ * M / 4 ≤ |ξ|) :
    2 ≤ M ^ (-(1 / 18 : ℝ)) * (1 + |ξ|) ^ (1 / 18 : ℝ) * (32 * δ ^ (-(1 / 18 : ℝ))) := by
  have hμ : 0 < μ := lt_of_lt_of_le hδ hμδ
  have h1 : (δ / 4) ^ (1 / 18 : ℝ) * M ^ (1 / 18 : ℝ) ≤ (1 + |ξ|) ^ (1 / 18 : ℝ) := by
    rw [← Real.mul_rpow (by positivity) hM.le]
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    have : δ / 4 * M ≤ μ * M / 4 := by nlinarith
    linarith [abs_nonneg ξ]
  have h4 : (1 / 4 : ℝ) ≤ (1 / 4 : ℝ) ^ (1 / 18 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_ge (x := (1 / 4 : ℝ)) (y := 1) (z := 1 / 18) (by norm_num) (by norm_num)
      (by norm_num)
    simpa using this
  have hsplit : (δ / 4) ^ (1 / 18 : ℝ) = (1 / 4 : ℝ) ^ (1 / 18 : ℝ) * δ ^ (1 / 18 : ℝ) := by
    rw [div_eq_mul_inv, mul_comm, ← Real.mul_rpow (by norm_num) hδ.le]; norm_num
  have hδδ : δ ^ (1 / 18 : ℝ) * δ ^ (-(1 / 18 : ℝ)) = 1 := by rw [← Real.rpow_add hδ]; norm_num
  have hMM : M ^ (-(1 / 18 : ℝ)) * M ^ (1 / 18 : ℝ) = 1 := by rw [← Real.rpow_add hM]; norm_num
  have hp : 0 ≤ M ^ (-(1 / 18 : ℝ)) * (32 * δ ^ (-(1 / 18 : ℝ))) := by positivity
  calc (2 : ℝ) ≤ 32 * (1 / 4) := by norm_num
    _ ≤ 32 * (1 / 4 : ℝ) ^ (1 / 18 : ℝ) := by gcongr
    _ = M ^ (-(1 / 18 : ℝ)) * ((δ / 4) ^ (1 / 18 : ℝ) * M ^ (1 / 18 : ℝ)) * (32 * δ ^ (-(1 / 18 : ℝ))) := by
        rw [hsplit]
        calc 32 * (1 / 4 : ℝ) ^ (1 / 18 : ℝ)
            = 32 * (1 / 4 : ℝ) ^ (1 / 18 : ℝ) * (δ ^ (1 / 18 : ℝ) * δ ^ (-(1 / 18 : ℝ))) *
                (M ^ (-(1 / 18 : ℝ)) * M ^ (1 / 18 : ℝ)) := by rw [hδδ, hMM]; ring
          _ = _ := by ring
    _ ≤ M ^ (-(1 / 18 : ℝ)) * (1 + |ξ|) ^ (1 / 18 : ℝ) * (32 * δ ^ (-(1 / 18 : ℝ))) := by
        gcongr

/-- Tiny regime with `μM < 2`: `1 ≤ M^{−1/18} · 32 δ^{−1/18}`. -/
theorem atom_tiny_small {M μ δ : ℝ} (hδ : 0 < δ) (hμδ : δ ≤ μ) (hM : 0 < M) (hμM : μ * M < 2) :
    1 ≤ M ^ (-(1 / 18 : ℝ)) * (32 * δ ^ (-(1 / 18 : ℝ))) := by
  have hμ : 0 < μ := lt_of_lt_of_le hδ hμδ
  have hM2 : M ≤ 2 / δ := by
    rw [le_div_iff₀ hδ]; nlinarith
  have h1 : M ^ (1 / 18 : ℝ) ≤ (2 / δ) ^ (1 / 18 : ℝ) := Real.rpow_le_rpow hM.le hM2 (by norm_num)
  have h2 : (2 / δ) ^ (1 / 18 : ℝ) = 2 ^ (1 / 18 : ℝ) * δ ^ (-(1 / 18 : ℝ)) := by
    rw [div_eq_mul_inv, Real.mul_rpow (by norm_num) (inv_nonneg.2 hδ.le), Real.inv_rpow hδ.le,
      ← Real.rpow_neg hδ.le]
  have h3 : (2 : ℝ) ^ (1 / 18 : ℝ) ≤ 32 := by
    calc (2 : ℝ) ^ (1 / 18 : ℝ) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ ≤ 32 := by norm_num
  have hMM : M ^ (-(1 / 18 : ℝ)) * M ^ (1 / 18 : ℝ) = 1 := by rw [← Real.rpow_add hM]; norm_num
  have hp : 0 ≤ M ^ (-(1 / 18 : ℝ)) := Real.rpow_nonneg hM.le _
  calc (1 : ℝ) = M ^ (-(1 / 18 : ℝ)) * M ^ (1 / 18 : ℝ) := hMM.symm
    _ ≤ M ^ (-(1 / 18 : ℝ)) * (2 ^ (1 / 18 : ℝ) * δ ^ (-(1 / 18 : ℝ))) := by rw [← h2]; gcongr
    _ ≤ M ^ (-(1 / 18 : ℝ)) * (32 * δ ^ (-(1 / 18 : ℝ))) := by
        gcongr

/-- **The tiny-δ core**: `(δ/(2L^{d−γ}))^n (2L+1)^{d·b} (32δ^{−1/18})^n ≤ (δ^{10ν}/L)^n` for `b ≤ 2n` and
`δ ≤ L^{−(12d+14)}`. -/
theorem tiny_core {L δ ν γ d : ℝ} {n b : ℕ} (hL : 2 ≤ L) (hd : 1 ≤ d) (hδ : 0 < δ)
    (hδL : δ ≤ L ^ (-(12 * d + 14))) (_hν : 0 ≤ ν) (hν1 : 40 * ν ≤ 1 / 100) (hγ : γ ≤ 2) (hb : b ≤ 2 * n)
    (dn : ℕ) (hdn : (dn : ℝ) = d) :
    (δ / (2 * L ^ (d - γ))) ^ n * (2 * L + 1) ^ (dn * b) * (32 * δ ^ (-(1 / 18 : ℝ))) ^ n ≤
      (δ ^ (10 * ν) / L) ^ n := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hδ1 : δ ≤ 1 := hδL.trans (Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith))
  -- (2L+1)^{d b} ≤ (L^{6d})^n
  have h3 : 2 * L + 1 ≤ L ^ (3 : ℕ) := by
    have h4 : 4 ≤ L * L := by nlinarith
    have : L ^ (3 : ℕ) = L * (L * L) := by ring
    rw [this]; nlinarith
  have hpow : (2 * L + 1) ^ (dn * b) ≤ (L ^ (6 * d)) ^ n := by
    calc (2 * L + 1) ^ (dn * b) ≤ (2 * L + 1) ^ (dn * (2 * n)) :=
          pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_left _ hb)
      _ ≤ (L ^ (3 : ℕ)) ^ (dn * (2 * n)) := pow_le_pow_left₀ (by linarith) h3 _
      _ = (L ^ (6 * d)) ^ n := by
          have e1 : (L ^ (6 * d)) ^ n = L ^ (6 * dn * n) := by
            rw [← hdn, show (6 * (dn : ℝ)) = ((6 * dn : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, ← pow_mul]
          rw [e1, ← pow_mul]; congr 1; ring
  -- per unit
  have hunit : δ / (2 * L ^ (d - γ)) * L ^ (6 * d) * (32 * δ ^ (-(1 / 18 : ℝ))) ≤ δ ^ (10 * ν) / L := by
    have hA : δ ^ (17 / 18 - 10 * ν) * δ ^ (10 * ν) = δ * δ ^ (-(1 / 18 : ℝ)) := by
      rw [show δ * δ ^ (-(1 / 18 : ℝ)) = δ ^ (1 : ℝ) * δ ^ (-(1 / 18 : ℝ)) by rw [Real.rpow_one],
        ← Real.rpow_add hδ, ← Real.rpow_add hδ]
      congr 1; ring
    have hB : L ^ (6 * d - (d - γ)) = L ^ (6 * d) / L ^ (d - γ) := Real.rpow_sub hL0 _ _
    have hLp : 0 < L ^ (d - γ) := Real.rpow_pos_of_pos hL0 _
    have e : δ / (2 * L ^ (d - γ)) * L ^ (6 * d) * (32 * δ ^ (-(1 / 18 : ℝ))) =
        16 * (δ ^ (17 / 18 - 10 * ν) * δ ^ (10 * ν)) * L ^ (6 * d - (d - γ)) := by
      rw [hA, hB]
      field_simp
      ring
    rw [e]
    have hδa : δ ^ (17 / 18 - 10 * ν) ≤ δ ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (x := δ) (y := 17 / 18 - 10 * ν) (z := 1 / 2) hδ hδ1 (by linarith)
    have hδb : δ ^ (1 / 2 : ℝ) ≤ L ^ (-(6 * d + 7)) := by
      calc δ ^ (1 / 2 : ℝ) ≤ (L ^ (-(12 * d + 14))) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hδ.le hδL (by norm_num)
        _ = L ^ (-(6 * d + 7)) := by rw [← Real.rpow_mul hL0.le]; congr 1; ring
    have hLe : L ^ (6 * d - (d - γ)) ≤ L ^ (6 * d + 2) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have hL5 : 16 * L ^ (-(4 : ℝ)) ≤ 1 := by
      have h1 : L ^ (-(4 : ℝ)) ≤ (2 : ℝ) ^ (-(4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hL (by norm_num)
      have h2 : (2 : ℝ) ^ (-(4 : ℝ)) = 1 / 16 := by norm_num
      calc 16 * L ^ (-(4 : ℝ)) ≤ 16 * (2 : ℝ) ^ (-(4 : ℝ)) := by gcongr
        _ = 1 := by rw [h2]; norm_num
    have hp1 : 0 ≤ δ ^ (10 * ν) := Real.rpow_nonneg hδ.le _
    calc 16 * (δ ^ (17 / 18 - 10 * ν) * δ ^ (10 * ν)) * L ^ (6 * d - (d - γ))
        ≤ 16 * (L ^ (-(6 * d + 7)) * δ ^ (10 * ν)) * L ^ (6 * d + 2) := by
          gcongr; exact hδa.trans hδb
      _ = (16 * L ^ (-(4 : ℝ))) * (δ ^ (10 * ν) / L) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg_one]
          have : L ^ (-(6 * d + 7)) * L ^ (6 * d + 2) = L ^ (-(4 : ℝ)) * L ^ (-1 : ℝ) := by
            rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; congr 1; ring
          calc 16 * (L ^ (-(6 * d + 7)) * δ ^ (10 * ν)) * L ^ (6 * d + 2)
              = 16 * (L ^ (-(6 * d + 7)) * L ^ (6 * d + 2)) * δ ^ (10 * ν) := by ring
            _ = _ := by rw [this]; ring
      _ ≤ 1 * (δ ^ (10 * ν) / L) := by gcongr
      _ = δ ^ (10 * ν) / L := one_mul _
  calc (δ / (2 * L ^ (d - γ))) ^ n * (2 * L + 1) ^ (dn * b) * (32 * δ ^ (-(1 / 18 : ℝ))) ^ n
      ≤ (δ / (2 * L ^ (d - γ))) ^ n * (L ^ (6 * d)) ^ n * (32 * δ ^ (-(1 / 18 : ℝ))) ^ n := by
        gcongr
    _ = (δ / (2 * L ^ (d - γ)) * L ^ (6 * d) * (32 * δ ^ (-(1 / 18 : ℝ)))) ^ n := by
        rw [← mul_pow, ← mul_pow]
    _ ≤ (δ ^ (10 * ν) / L) ^ n := pow_le_pow_left₀ (by positivity) hunit n

end WaveTurbulence.Flower.SelRes
