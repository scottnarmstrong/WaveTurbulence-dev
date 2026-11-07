/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.FreeBound
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Final
/-! FLOWER-P7: exponent bookkeeping for the `dt = false` (kind `L0`) decapitation bound. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open TTree Finset LGSpine

section
variable {C₀ : ℕ} {P : WTParams} {p N : ℕ} {Rr : ℕ → Mom P.d → ℝ} {k : Mom P.d} {Creg : ℕ → ℝ} {Cr : ℝ}

/-- **The `kind = L0`, `dt = false` couple bound by decapitation** (loss as a hypothesis on the data counts):
`‖coupleSum … L0 false‖ ≤ ⟨k⟩^{-4Λ} L^{100d} δ^{2νN}`. -/
theorem coupleSum_false_bound
    (Hs : ∀ tt : Fin (2 * 3) → ℝ, (∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) → PieceHyp C₀ P p N Rr k tt Creg)
    (hb : BoundNum P Creg Cr)
    (hF : ∀ q : ℕ, Summable fun n : Fin P.d → ℤ => |inputsF P Rr q (k + latticePoint P.L n)|) (t : ℝ)
    (hΛ : (P.d : ℝ) + 1 ≤ 4 * P.Lambda (p + 1))
    (hLoss : Qn P p N Cr * 12 * 3 ^ (4 * (P.Lambda (p + 1) : ℝ)) * (Kd P.d * P.L ^ (P.d + 1)) ^ 6 ≤
      P.L ^ (100 * P.d : ℝ)) :
    ‖coupleSum P (inputsF P Rr) p N .L0 false t k‖ ≤
      jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (2 * P.ν * (N : ℝ)) := by
  refine (coupleSum_false_norm_le Hs hb t hΛ hF).trans ?_
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
