/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Assembly
/-! FLOWER-P7: exponent bookkeeping for the decapitation bound: `δ² · δ^{2ν(N-2)} ≤ δ^{2νN}`, the coupling
`c² ≤ δ²/4`, and the loss `L^{100d}`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open TTree Finset LGSpine

/-- The constant of the label sum: `Σ' gw ≤ Kd d · L^{d+1}`. -/
noncomputable def Kd (d : ℕ) : ℝ :=
  max 1 ((Real.sqrt 2 * Real.sqrt (1 + d)) ^ (d + 1) * (Real.sqrt 2) ^ (d + 1) *
    ∑' m : Fin d → ℤ, ((1 + ‖m‖) ^ (d + 1))⁻¹)

theorem one_le_Kd (d : ℕ) : 1 ≤ Kd d := le_max_left _ _

theorem tsum_gw_le_Kd {d : ℕ} {L : ℝ} (hL : 1 ≤ L) (k : Mom d) {a : ℝ} (ha : (d : ℝ) + 1 ≤ a) :
    ∑' m, gw L k a m ≤ Kd d * L ^ (d + 1) := by
  refine (tsum_gw_le hL k ha).trans ?_
  have h1 := latSum_le (d := d) hL
  have hc : 0 ≤ (Real.sqrt 2 * Real.sqrt (1 + d)) ^ (d + 1) := by positivity
  calc (Real.sqrt 2 * Real.sqrt (1 + d)) ^ (d + 1) * latSum d L
      ≤ (Real.sqrt 2 * Real.sqrt (1 + d)) ^ (d + 1) *
          ((Real.sqrt 2 * L) ^ (d + 1) * ∑' m : Fin d → ℤ, ((1 + ‖m‖) ^ (d + 1))⁻¹) :=
        mul_le_mul_of_nonneg_left h1 hc
    _ = ((Real.sqrt 2 * Real.sqrt (1 + d)) ^ (d + 1) * (Real.sqrt 2) ^ (d + 1) *
          ∑' m : Fin d → ℤ, ((1 + ‖m‖) ^ (d + 1))⁻¹) * L ^ (d + 1) := by
        rw [mul_pow (Real.sqrt 2) L]; ring
    _ ≤ Kd d * L ^ (d + 1) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

theorem coupling_sq_le {P : WTParams} (hδ : 0 < P.δ) (hL : 1 ≤ P.L) (hγ : P.γ ≤ P.d) :
    (coupling P.d P.L P.γ P.δ) ^ 2 ≤ P.δ ^ 2 / 4 := by
  unfold coupling
  have h1 : (1 : ℝ) ≤ P.L ^ ((P.d : ℝ) - P.γ) := Real.one_le_rpow hL (by linarith)
  have h2 : 0 ≤ P.δ / (2 * P.L ^ ((P.d : ℝ) - P.γ)) := by positivity
  have h3 : P.δ / (2 * P.L ^ ((P.d : ℝ) - P.γ)) ≤ P.δ / 2 := by
    apply div_le_div_of_nonneg_left hδ.le (by norm_num) (by linarith)
  calc _ ≤ (P.δ / 2) ^ 2 := pow_le_pow_left₀ h2 h3 2
    _ = _ := by ring

theorem delta_sq_mul_le {P : WTParams} {Creg : ℕ → ℝ} {Cr : ℝ} (hb : BoundNum P Creg Cr) (N : ℕ) :
    P.δ ^ 2 * P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) ≤ P.δ ^ (2 * P.ν * (N : ℝ)) := by
  have h2 : P.δ ^ 2 = P.δ ^ ((2 : ℝ)) := by rw [Real.rpow_two]
  rw [h2, ← Real.rpow_add hb.hδ0]
  apply Real.rpow_le_rpow_of_exponent_ge hb.hδ0 hb.hδ1
  rcases le_or_gt 2 N with h | h
  · have : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by rw [Nat.cast_sub h]; norm_num
    rw [this]; nlinarith [hb.hν8, hb.hν]
  · have h1 : (N : ℝ) ≤ 1 := by
      have : N ≤ 1 := by omega
      exact_mod_cast this
    have : N - 2 = 0 := by omega
    rw [this]
    simp only [Nat.cast_zero, mul_zero, add_zero]
    nlinarith [hb.hν8, hb.hν, (Nat.cast_nonneg N : (0:ℝ) ≤ N)]

section
variable {C₀ : ℕ} {P : WTParams} {p N : ℕ} {Rr : ℕ → Mom P.d → ℝ} {k : Mom P.d} {t : ℝ} {Creg : ℕ → ℝ} {Cr : ℝ}

/-- **The `dt = true` couple bound, in the shape of `RegularCouplesDtAt`** (with the loss as a hypothesis on the
data counts): `‖coupleSum … true‖ ≤ ⟨k⟩^{-4Λ} L^{100d} δ^{2νN}`. -/
theorem coupleSum_true_bound (H : PieceHyp C₀ P p N Rr k (fun _ => t) Creg) (hb : BoundNum P Creg Cr) (kind : TreeKind)
    (hΛ : (P.d : ℝ) + 1 ≤ 4 * P.Lambda (p + 1))
    (hLoss : Qn P p N Cr * 12 * 3 ^ (4 * (P.Lambda (p + 1) : ℝ)) * (Kd P.d * P.L ^ (P.d + 1)) ^ 6 ≤
      P.L ^ (100 * P.d : ℝ)) :
    ‖coupleSum P (inputsF P Rr) p N kind true t k‖ ≤
      jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (2 * P.ν * (N : ℝ)) := by
  refine (coupleSum_true_norm_le H hb kind hΛ).trans ?_
  set a : ℝ := 4 * P.Lambda (p + 1) with ha
  set G : ℝ := P.δ ^ (2 * P.ν * ((N - 2 : ℕ) : ℝ)) with hG
  set J : ℝ := jbr k ^ (-a) with hJ
  set Mg : ℝ := max 1 (∑' m, gw P.L k a m) with hMg
  have hG0 : 0 ≤ G := Real.rpow_nonneg hb.hδ0.le _
  have hJ0 : 0 ≤ J := Real.rpow_nonneg (WaveTurbulence.Induct.jbr_pos k).le _
  have hQ := Qn_pos P p N hb.hCr0
  have h3 : (0 : ℝ) ≤ 3 ^ a := Real.rpow_nonneg (by norm_num) _
  have hKL : 1 ≤ Kd P.d * P.L ^ (P.d + 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_Kd _) (one_le_pow₀ hb.hL)
  have hMg1 : Mg ≤ Kd P.d * P.L ^ (P.d + 1) :=
    max_le hKL (tsum_gw_le_Kd hb.hL k hΛ)
  have hMg0 : 0 ≤ Mg := le_trans zero_le_one (le_max_left _ _)
  have hMg6 : Mg ^ 6 ≤ (Kd P.d * P.L ^ (P.d + 1)) ^ 6 := pow_le_pow_left₀ hMg0 hMg1 6
  have hcsq := coupling_sq_le hb.hδ0 hb.hL hb.hγ
  have hX : 0 ≤ Qn P p N Cr * G * (16 * (3 * (3 ^ a * J) * Mg ^ 6)) := by
    have : 0 ≤ Mg ^ 6 := by positivity
    have : 0 ≤ Qn P p N Cr := by linarith
    positivity
  have hδG := delta_sq_mul_le hb N
  calc (coupling P.d P.L P.γ P.δ) ^ 2 * (Qn P p N Cr * G * (16 * (3 * (3 ^ a * J) * Mg ^ 6)))
      ≤ (P.δ ^ 2 / 4) * (Qn P p N Cr * G * (16 * (3 * (3 ^ a * J) * Mg ^ 6))) :=
        mul_le_mul_of_nonneg_right hcsq hX
    _ = (P.δ ^ 2 * G) * J * (Qn P p N Cr * 12 * 3 ^ a * Mg ^ 6) := by ring
    _ ≤ P.δ ^ (2 * P.ν * (N : ℝ)) * J * P.L ^ (100 * P.d : ℝ) := by
        have hL1 : Qn P p N Cr * 12 * 3 ^ a * Mg ^ 6 ≤ P.L ^ (100 * P.d : ℝ) := by
          refine le_trans ?_ hLoss
          have : 0 ≤ Qn P p N Cr := by linarith
          have : 0 ≤ Qn P p N Cr * 12 * 3 ^ a := by positivity
          exact mul_le_mul_of_nonneg_left hMg6 this
        have hnn : 0 ≤ Qn P p N Cr * 12 * 3 ^ a * Mg ^ 6 := by
          have : 0 ≤ Qn P p N Cr := by linarith
          positivity
        calc (P.δ ^ 2 * G) * J * (Qn P p N Cr * 12 * 3 ^ a * Mg ^ 6)
            ≤ (P.δ ^ (2 * P.ν * (N : ℝ))) * J * (Qn P p N Cr * 12 * 3 ^ a * Mg ^ 6) := by
              apply mul_le_mul_of_nonneg_right _ hnn
              exact mul_le_mul_of_nonneg_right hδG hJ0
          _ ≤ (P.δ ^ (2 * P.ν * (N : ℝ))) * J * P.L ^ (100 * P.d : ℝ) :=
              mul_le_mul_of_nonneg_left hL1 (mul_nonneg (Real.rpow_nonneg hb.hδ0.le _) hJ0)
    _ = _ := by ring

end

end WaveTurbulence.FlowerP7
