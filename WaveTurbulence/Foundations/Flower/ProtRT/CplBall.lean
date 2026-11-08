/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.CplAsm
public import WaveTurbulence.Foundations.Flower.ProtPin.FinalTwo
public import WaveTurbulence.Foundations.Flower.ProtPin.TermStarFinal
public import WaveTurbulence.Foundations.Flower.ProtPin.RootPack

/-! # RT-GATE (ii): the couple clause on one lattice ball, from `RtOne` and `RtBoth`

On the R189 box a pinned tree does not read its clock (`rt_kernel_up2`): with one pinned root the kernel is a function
of the partner clock (`rn_lift2`, `rt_rn_lift0`) bounded by `RtOne`; with both pinned it is a constant bounded by
`RtBoth`. D3's output weight gives `⟨k⟩^{-30d} (latC L^d)²` (`rt_tcWt_le`), hence `4^d ⟨c₀⟩^{-2d}` on the ball
(`rt_ball_wt`); the two-cut budget is at most `L²` times the one-cut budget (`rt_two_le_term`). Per output:
`Cr · L² · termRb(c') · ⟨c₀⟩^{-2d}`; the local output extension and D3's `term_star_alg` give
`L^{31d+4c'+4} · regBound`, `≤ L^{47d+5}` as `c' ≤ 4d`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **Lift in the first clock**: a function of the first clock alone. -/
theorem rt_rn_lift0 {θ : ℝ} (hθ : 0 ≤ θ) (p q' : ℝ) {B : Set (Fin 2 → ℝ)} (hB : B ⊆ timeBox p q')
    (f : (Fin 1 → ℝ) → ℂ) :
    rn θ B (fun ts => f (fun _ => ts 0)) ≤ cutNorm θ * rn θ (win p) f := by
  have key : ∀ g : (Fin 1 → ℝ) → ℂ, (∀ T ∈ win p, g T = f T) →
      rn θ B (fun ts => f (fun _ => ts 0)) ≤ cutNorm θ * timeFourierNorm θ g := by
    intro g hg
    refine (rn_le θ (g := fun ts => g (fun _ => ts 0) * cut1 q' (fun _ => ts 1)) fun ts hts => ?_).trans ?_
    · rw [cut1_eq_one (hB hts).2, mul_one]
      exact hg _ (hB hts).1
    · refine (timeFourierNorm_tensor2_le hθ g (cut1 q')).trans ?_
      rw [cut1_norm, mul_comm]
  by_cases h0 : cutNorm θ = 0
  · refine (key f fun _ _ => rfl).trans ?_
    rw [h0, zero_mul]
    exact zero_le
  conv_rhs => rw [rn_eq_iInf]
  rw [ENNReal.mul_iInf_of_ne h0 (cutNorm_lt_top θ).ne]
  refine le_iInf fun g => ?_
  rw [ENNReal.mul_iInf_of_ne h0 (cutNorm_lt_top θ).ne]
  exact le_iInf fun hg => key g hg

theorem rt_gateM_empty {w d : ℕ} {G : Garden w} (S : Finset (GNode G.tree)) (ω : GNode G.tree → Flower.IncTop.Star d → ℂ)
    (L : ℝ) : gateM S ω (∅ : Finset (GBranch G.tree)) (fun _ => L) ∅ (fun _ => L) =
      fun κ => Flower.IncTop.starWeight S ω κ := by
  funext κ
  simp [gateM, filtWeight]

/-- **The two-cut budget is at most `L²` times the one-cut budget.** -/
theorem rt_two_le_term {P : WTParams} {CL Cr : ℝ} (hL : 1 ≤ P.L) (hδ : 0 ≤ P.δ) (hC11 : 1 ≤ P.C₁)
    (hδC : P.δ * P.C₁ ≤ 1) (hCLCr : 1 ≤ CL * Cr)
    (hbig : termK CL Cr P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ)) {n : ℕ} (hn1 : 1 ≤ n) (g : ℕ)
    {leaf CS : ℝ} (hleaf : 0 ≤ leaf) (hCS : 0 ≤ CS) :
    twoRb P 0 n g leaf CS ≤ P.L ^ 2 * termRb P 0 n g leaf CS := by
  have hL0 : 0 < P.L := by linarith
  have hC1 : 0 ≤ P.C₁ := by linarith
  set A := coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 with hA
  have hAe : A = latC P.d ^ 2 * (P.δ ^ 2 / 4 * P.L ^ (2 * P.γ)) := by
    rw [hA, ← coupling_sq_mul hL0]; ring
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hLγ : 0 ≤ P.L ^ (2 * P.γ) := Real.rpow_nonneg hL0.le _
  have hL2 : P.L ^ (2 : ℝ) = P.L ^ 2 := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hK : latC P.d ^ 2 / 4 ≤ termK CL Cr P.d := by
    unfold termK
    have : 0 ≤ latC P.d ^ 2 / 4 := by positivity
    calc latC P.d ^ 2 / 4 = 1 * (latC P.d ^ 2 / 4) := (one_mul _).symm
      _ ≤ (CL * Cr) * (latC P.d ^ 2 / 4) := mul_le_mul_of_nonneg_right hCLCr this
      _ = _ := by ring
  -- `A C₁² ≤ δ L²`
  have hAC : A * P.C₁ ^ 2 ≤ P.δ * P.L ^ 2 := by
    rw [hAe]
    have h1 : latC P.d ^ 2 / 4 * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ 2 := by
      refine le_trans ?_ (hL2 ▸ hbig)
      have : 0 ≤ P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) := by positivity
      calc latC P.d ^ 2 / 4 * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) =
          (latC P.d ^ 2 / 4) * (P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ)) := by ring
        _ ≤ termK CL Cr P.d * (P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ)) := mul_le_mul_of_nonneg_right hK this
        _ = _ := by ring
    calc latC P.d ^ 2 * (P.δ ^ 2 / 4 * P.L ^ (2 * P.γ)) * P.C₁ ^ 2 =
        P.δ * (latC P.d ^ 2 / 4 * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ)) := by ring
      _ ≤ P.δ * P.L ^ 2 := mul_le_mul_of_nonneg_left h1 hδ
  have hrb := rb_nonneg hC1 hδ hL0.le (n - 2) g
  -- the key inequality `A C₁³ rb(n−2) ≤ L² rb(n−1)`
  have hkey : A * (P.C₁ ^ 3 * rb P (n - 2) g) ≤ P.L ^ 2 * rb P (n - 1) g := by
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have e1 : n - 2 = n - 1 := by omega
      rw [e1]
      have hr1 := rb_nonneg hC1 hδ hL0.le (n - 1) g
      have : A * P.C₁ ^ 3 ≤ P.L ^ 2 := by
        calc A * P.C₁ ^ 3 = (A * P.C₁ ^ 2) * P.C₁ := by ring
          _ ≤ (P.δ * P.L ^ 2) * P.C₁ := mul_le_mul_of_nonneg_right hAC hC1
          _ = (P.δ * P.C₁) * P.L ^ 2 := by ring
          _ ≤ 1 * P.L ^ 2 := mul_le_mul_of_nonneg_right hδC (by positivity)
          _ = P.L ^ 2 := one_mul _
      calc A * (P.C₁ ^ 3 * rb P (n - 1) g) = (A * P.C₁ ^ 3) * rb P (n - 1) g := by ring
        _ ≤ P.L ^ 2 * rb P (n - 1) g := mul_le_mul_of_nonneg_right this hr1
    · have e1 : rb P (n - 1) g = P.C₁ * P.δ * rb P (n - 2) g := by
        rw [rb_succ P (by omega : 1 ≤ n - 1), show n - 1 - 1 = n - 2 by omega]
      rw [e1]
      calc A * (P.C₁ ^ 3 * rb P (n - 2) g) = (A * P.C₁ ^ 2) * (P.C₁ * rb P (n - 2) g) := by ring
        _ ≤ (P.δ * P.L ^ 2) * (P.C₁ * rb P (n - 2) g) :=
            mul_le_mul_of_nonneg_right hAC (mul_nonneg hC1 hrb)
        _ = _ := by ring
  unfold twoRb termRb
  simp only [Real.rpow_zero, mul_zero, one_mul, mul_one]
  have hX : 0 ≤ A * P.C₁ ^ 3 * leaf * CS := by positivity
  calc A ^ 2 * (P.C₁ ^ 6 * rb P (n - 2) g) * leaf * CS =
      (A * P.C₁ ^ 3 * leaf * CS) * (A * (P.C₁ ^ 3 * rb P (n - 2) g)) := by ring
    _ ≤ (A * P.C₁ ^ 3 * leaf * CS) * (P.L ^ 2 * rb P (n - 1) g) := mul_le_mul_of_nonneg_left hkey hX
    _ = _ := by rw [hA]; ring

end WaveTurbulence.Flower.ProtRT
