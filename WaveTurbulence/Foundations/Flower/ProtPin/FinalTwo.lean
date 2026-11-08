/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.RootPair
public import WaveTurbulence.Foundations.Flower.ProtPin.Alpha

/-! # D3 PROT-PIN: the budget of two cuts

Configurations with two cuts ((P3), (P5), (P7)) are needed at the weight `θ = η` only (`c = 31d + 6`). Their per-output
bound has the form `Cr · twoRb` with
`twoRb = L^a (c²(latC L^d)²)² C₁⁶ rb(n−2, g) · leaf · CS` (`a ≤ 1` pays a lost incoherency, `γ₁ − √η ≤ 1`); since
`c²(latC L^d)² = latC² δ²/4 L^{2γ}` and `rb(n) = (C₁δ)² rb(n−2)`, `final_two` closes it with LocalOutputExtension
(`L^{31d}`) once `K δ² C₁⁴ L^{4γ} ≤ L⁵` (`big2_of_large`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut

/-- The two-cut budget at one output. -/
def twoRb (P : WTParams) (a : ℝ) (n g : ℕ) (leaf CS : ℝ) : ℝ :=
  P.L ^ a * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2) ^ 2 * (P.C₁ ^ 6 * rb P (n - 2) g) * leaf * CS

theorem twoRb_nonneg {P : WTParams} (hC1 : 0 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 0 ≤ P.L) (a : ℝ) (n g : ℕ)
    {leaf CS : ℝ} (hleaf : 0 ≤ leaf) (hCS : 0 ≤ CS) : 0 ≤ twoRb P a n g leaf CS := by
  unfold twoRb
  have := rb_nonneg hC1 hδ hL (n - 2) g
  have := Real.rpow_nonneg hL a
  positivity

/-- The two-cut constant. -/
def twoK (CL Cr : ℝ) (d : ℕ) : ℝ := CL * Cr * latC d ^ 4 / 16

theorem twoK_nonneg {CL Cr : ℝ} (hCL : 0 ≤ CL) (hCr : 0 ≤ Cr) (d : ℕ) : 0 ≤ twoK CL Cr d := by
  unfold twoK
  have := latC_nonneg d
  positivity

/-- The size condition of two cuts. -/
theorem big2_of_large {K Kb L γ δ C : ℝ} (hK0 : 0 ≤ K) (hKK : K ≤ Kb) (hγ : γ < 1) (hL1 : 1 ≤ L)
    (hL : Kb ^ (1 / (5 - 4 * γ)) ≤ L) (hδ : 0 ≤ δ) (hδC : δ * C ^ 2 ≤ 1) :
    K * δ ^ 2 * C ^ 4 * L ^ (4 * γ) ≤ L ^ (5 : ℝ) := by
  have hL0 : 0 < L := by linarith
  have ha : 0 < 5 - 4 * γ := by linarith
  have hKb : 0 ≤ Kb := hK0.trans hKK
  have h1 : Kb ≤ L ^ (5 - 4 * γ) := by
    calc Kb = (Kb ^ (5 - 4 * γ)⁻¹) ^ (5 - 4 * γ) := (Real.rpow_inv_rpow hKb ha.ne').symm
      _ ≤ L ^ (5 - 4 * γ) := by
        refine Real.rpow_le_rpow (Real.rpow_nonneg hKb _) ?_ ha.le
        simpa only [one_div] using hL
  have hLg : 0 ≤ L ^ (4 * γ) := Real.rpow_nonneg hL0.le _
  have hδC2 : δ ^ 2 * C ^ 4 ≤ 1 := by
    have h0 : 0 ≤ δ * C ^ 2 := mul_nonneg hδ (by positivity)
    calc δ ^ 2 * C ^ 4 = (δ * C ^ 2) ^ 2 := by ring
      _ ≤ 1 := pow_le_one₀ h0 hδC
  calc K * δ ^ 2 * C ^ 4 * L ^ (4 * γ) = K * (δ ^ 2 * C ^ 4) * L ^ (4 * γ) := by ring
    _ ≤ K * 1 * L ^ (4 * γ) := by gcongr
    _ ≤ L ^ (5 - 4 * γ) * L ^ (4 * γ) := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_right (hKK.trans h1) hLg
    _ = L ^ (5 : ℝ) := by rw [← Real.rpow_add hL0]; ring_nf

/-- **From a per-output two-cut bound to the frozen norm.** -/
theorem final_two {θ : ℝ} {P : WTParams} {Cr CL c a : ℝ} (hL : 1 ≤ P.L) (hδ : 0 ≤ P.δ) (hC1 : 0 ≤ P.C₁)
    (hCr : 0 ≤ Cr) (hCL : 0 ≤ CL) (ha : a ≤ 1) (hc : 31 * (P.d : ℝ) + 6 ≤ c)
    (hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d) (F : (Fin r → ℝ) → Mom P.d → ℂ)
      (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
      XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
    (hbig2 : twoK CL Cr P.d * P.δ ^ 2 * P.C₁ ^ 4 * P.L ^ (4 * P.γ) ≤ P.L ^ (5 : ℝ))
    {r : ℕ} (Bx : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d) (Fk : (Fin r → ℝ) → Mom P.d → ℂ) {n g : ℕ} (hn2 : 2 ≤ n)
    {leaf CS : ℝ} (hleaf : 0 ≤ leaf) (hCS : 0 ≤ CS)
    (hperk : ∀ k, rn θ Bx (fun ts => Fk ts k) ≤ ENNReal.ofReal (Cr * twoRb P a n g leaf CS)) :
    XNormRestr θ (30 * P.d) 0 Bx (latticeBall P.L b₀ c₀) Fk ≤
      ENNReal.ofReal CS * ENNReal.ofReal (P.L ^ c) * regBound P n g * ENNReal.ofReal leaf := by
  have hL0 : 0 < P.L := by linarith
  have hr := rb_nonneg hC1 hδ hL0.le (n - 2) g
  refine (hLOE P.L hL Bx b₀ c₀ Fk _ fun k _ => (XNorm00Restr_single_le_rn θ _ _ k).trans (hperk k)).trans ?_
  have hLc : 0 ≤ P.L ^ c := Real.rpow_nonneg hL0.le _
  have hrn : rb P n g = (P.C₁ * P.δ) ^ 2 * rb P (n - 2) g := by
    rw [rb_succ P (by omega : 1 ≤ n), rb_succ P (by omega : 1 ≤ n - 1), show n - 1 - 1 = n - 2 by omega]
    ring
  have hrb0 : 0 ≤ rb P n g := by rw [hrn]; positivity
  rw [← ENNReal.ofReal_mul (mul_nonneg hCL (pow_nonneg hL0.le _)), regBound_eq_rb,
    ← ENNReal.ofReal_mul hCS, ← ENNReal.ofReal_mul (mul_nonneg hCS hLc),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCS hLc) hrb0)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e1 : coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 =
      latC P.d ^ 2 * (P.δ ^ 2 / 4 * P.L ^ (2 * P.γ)) := by
    rw [← coupling_sq_mul hL0]; ring
  have e2 : (P.L ^ (2 * P.γ)) ^ 2 = P.L ^ (4 * P.γ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; ring_nf
  have hLa : P.L ^ a ≤ P.L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL ha
  have hL31 : (P.L ^ (31 * P.d) : ℝ) = P.L ^ ((31 * P.d : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
  have hcc : P.L ^ ((31 * P.d : ℕ) : ℝ) * P.L ^ (5 : ℝ) * P.L ^ (1 : ℝ) ≤ P.L ^ c := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
    refine Real.rpow_le_rpow_of_exponent_le hL ?_
    push_cast; linarith
  have hX : 0 ≤ P.C₁ ^ 2 * P.δ ^ 2 * rb P (n - 2) g * leaf * CS := by positivity
  have hK := twoK_nonneg hCL hCr P.d
  calc CL * P.L ^ (31 * P.d) * (Cr * twoRb P a n g leaf CS)
      = (twoK CL Cr P.d * P.δ ^ 2 * P.C₁ ^ 4 * P.L ^ (4 * P.γ)) * P.L ^ (31 * P.d) * P.L ^ a *
          (P.C₁ ^ 2 * P.δ ^ 2 * rb P (n - 2) g * leaf * CS) := by
        unfold twoRb twoK
        rw [e1]
        have : (latC P.d ^ 2 * (P.δ ^ 2 / 4 * P.L ^ (2 * P.γ))) ^ 2 =
            latC P.d ^ 4 * P.δ ^ 4 / 16 * (P.L ^ (2 * P.γ)) ^ 2 := by ring
        rw [this, e2]
        ring
    _ ≤ P.L ^ (5 : ℝ) * P.L ^ (31 * P.d) * P.L ^ (1 : ℝ) * (P.C₁ ^ 2 * P.δ ^ 2 * rb P (n - 2) g * leaf * CS) := by
        refine mul_le_mul_of_nonneg_right ?_ hX
        exact mul_le_mul (mul_le_mul_of_nonneg_right hbig2 (pow_nonneg hL0.le _)) hLa
          (Real.rpow_nonneg hL0.le _) (mul_nonneg (Real.rpow_nonneg hL0.le _) (pow_nonneg hL0.le _))
    _ = (P.L ^ ((31 * P.d : ℕ) : ℝ) * P.L ^ (5 : ℝ) * P.L ^ (1 : ℝ)) *
          (P.C₁ ^ 2 * P.δ ^ 2 * rb P (n - 2) g * leaf * CS) := by rw [hL31]; ring
    _ ≤ P.L ^ c * (P.C₁ ^ 2 * P.δ ^ 2 * rb P (n - 2) g * leaf * CS) := mul_le_mul_of_nonneg_right hcc hX
    _ = CS * P.L ^ c * rb P n g * leaf := by rw [hrn]; ring

/-- A lost incoherency costs at most `L`. -/
theorem rb_pred_le {P : WTParams} (hL : 1 ≤ P.L) (hC1 : 0 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hη : 0 ≤ P.η) (n : ℕ) {g : ℕ}
    (hg : 1 ≤ g) : rb P n (g - 1) ≤ P.L ^ (1 : ℝ) * rb P n g := by
  unfold rb
  have hL0 : 0 < P.L := by linarith
  have hg1 : P.gamma1 ≤ 1 := by
    unfold WTParams.gamma1
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hs : 0 ≤ Real.sqrt P.η := Real.sqrt_nonneg _
  have e : P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((g - 1 : ℕ) : ℝ)) =
      P.L ^ (P.gamma1 - Real.sqrt P.η) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) := by
    rw [← Real.rpow_add hL0]
    congr 1
    rw [Nat.cast_sub hg]
    push_cast; ring
  rw [e]
  have h1 : P.L ^ (P.gamma1 - Real.sqrt P.η) ≤ P.L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hA : 0 ≤ P.C₁ * (P.C₁ * P.δ) ^ n := by positivity
  have hB : 0 ≤ P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) := Real.rpow_nonneg hL0.le _
  calc P.C₁ * (P.C₁ * P.δ) ^ n * (P.L ^ (P.gamma1 - Real.sqrt P.η) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)))
      ≤ P.C₁ * (P.C₁ * P.δ) ^ n * (P.L ^ (1 : ℝ) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hB) hA
    _ = _ := by ring

end WaveTurbulence.Flower.ProtPin
