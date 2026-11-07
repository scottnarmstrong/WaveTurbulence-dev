/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.SmallGapCount
public import WaveTurbulence.Foundations.FinalCount.ErasePair
import Mathlib.Tactic

/-! # `SmallGapPairInput` (DH23 L1975)

`Δχ = −4` (`6` bonds, `2` atoms), the label count of `SmallGapCount`, and the exponent bookkeeping
`d + d(1−γ+η) + 2(d−γ) − 4(d−γ) = −(d−2)γ + dη ≤ −(γ₀ − dη)`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

theorem rpow_one_add' {L : ℝ} (hL : 0 < L) (a : ℝ) : L * L ^ a = L ^ (1 + a) := by
  rw [Real.rpow_add hL, Real.rpow_one]

theorem smallgap_arith {d : ℕ} (hd : 3 ≤ d) {γ η L C δ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (hη : 0 ≤ η) (hL : 1 ≤ L)
    (hC : 0 ≤ C) (hδ : 0 < δ) :
    ((⌈8 * ((2 * L + 1) ^ d * (2 * (L * L ^ (-γ + η)) + 1) ^ d * (C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))))⌉₊ : ℕ) : ℝ) *
        L ^ (-((d : ℝ) - γ) * ((4 : ℕ) : ℝ)) ≤
      (8 * 9 ^ d * C * δ⁻¹ + 1) * L ^ (-(min γ (1 - γ) - d * η)) := by
  have hLp : 0 < L := by linarith
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hg0 : min γ (1 - γ) ≤ γ := min_le_left _ _
  set lam := L ^ (-γ + η) with hlam
  have hLlam' : L * lam = L ^ (1 - γ + η) := by
    rw [hlam, rpow_one_add' hLp]; congr 1; ring
  have hLlam : 1 ≤ L * lam := by
    rw [hLlam']
    exact Real.one_le_rpow hL (by linarith [hγ.2])
  have h1 : (2 * L + 1) ^ d ≤ 3 ^ d * L ^ d := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) d
  have h2 : (2 * (L * lam) + 1) ^ d ≤ 3 ^ d * (L * lam) ^ d := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) d
  have hB : (2 * L + 1) ^ d * (2 * (L * lam) + 1) ^ d * (C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) ≤
      9 ^ d * (C * δ⁻¹) * (L ^ d * (L * lam) ^ d * L ^ (2 * ((d : ℝ) - γ))) := by
    have hpos : 0 ≤ C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)) := by positivity
    calc (2 * L + 1) ^ d * (2 * (L * lam) + 1) ^ d * (C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)))
        ≤ (3 ^ d * L ^ d) * (3 ^ d * (L * lam) ^ d) * (C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) := by
          gcongr
      _ = 9 ^ d * (C * δ⁻¹) * (L ^ d * (L * lam) ^ d * L ^ (2 * ((d : ℝ) - γ))) := by
          rw [show (9 : ℝ) ^ d = 3 ^ d * 3 ^ d by rw [← mul_pow]; norm_num]; ring
  have hexp : L ^ d * (L * lam) ^ d * L ^ (2 * ((d : ℝ) - γ)) * L ^ (-((d : ℝ) - γ) * ((4 : ℕ) : ℝ)) =
      L ^ (-(d : ℝ) * γ + d * η + 2 * γ) := by
    have e1 : L ^ d = L ^ (d : ℝ) := (Real.rpow_natCast L d).symm
    have e2 : (L * lam) ^ d = L ^ ((1 - γ + η) * d) := by
      rw [hLlam', ← Real.rpow_natCast, ← Real.rpow_mul hLp.le]
    rw [e1, e2, ← Real.rpow_add hLp, ← Real.rpow_add hLp, ← Real.rpow_add hLp]
    congr 1; push_cast; ring
  have hexp_le : L ^ (-(d : ℝ) * γ + d * η + 2 * γ) ≤ L ^ (-(min γ (1 - γ) - d * η)) :=
    Real.rpow_le_rpow_of_exponent_le hL (by nlinarith [hγ.1])
  have hexp2 : L ^ (-((d : ℝ) - γ) * ((4 : ℕ) : ℝ)) ≤ L ^ (-(min γ (1 - γ) - d * η)) :=
    Real.rpow_le_rpow_of_exponent_le hL (by push_cast; nlinarith [hγ.1, hγ.2, mul_nonneg (by positivity : (0 : ℝ) ≤ d) hη])
  have hceil := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 8 * ((2 * L + 1) ^ d * (2 * (L * lam) + 1) ^ d * (C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)))) by positivity)
  have hpow0 : 0 ≤ L ^ (-((d : ℝ) - γ) * ((4 : ℕ) : ℝ)) := Real.rpow_nonneg hLp.le _
  calc ((⌈8 * ((2 * L + 1) ^ d * (2 * (L * lam) + 1) ^ d * (C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))))⌉₊ : ℕ) : ℝ) *
        L ^ (-((d : ℝ) - γ) * ((4 : ℕ) : ℝ))
      ≤ (8 * ((2 * L + 1) ^ d * (2 * (L * lam) + 1) ^ d * (C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)))) + 1) *
        L ^ (-((d : ℝ) - γ) * ((4 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_right hceil.le hpow0
    _ ≤ (8 * (9 ^ d * (C * δ⁻¹) * (L ^ d * (L * lam) ^ d * L ^ (2 * ((d : ℝ) - γ)))) + 1) *
        L ^ (-((d : ℝ) - γ) * ((4 : ℕ) : ℝ)) := by gcongr
    _ = 8 * 9 ^ d * C * δ⁻¹ * (L ^ d * (L * lam) ^ d * L ^ (2 * ((d : ℝ) - γ)) * L ^ (-((d : ℝ) - γ) * ((4 : ℕ) : ℝ))) +
        L ^ (-((d : ℝ) - γ) * ((4 : ℕ) : ℝ)) := by ring
    _ = 8 * 9 ^ d * C * δ⁻¹ * L ^ (-(d : ℝ) * γ + d * η + 2 * γ) + L ^ (-((d : ℝ) - γ) * ((4 : ℕ) : ℝ)) := by rw [hexp]
    _ ≤ 8 * 9 ^ d * C * δ⁻¹ * L ^ (-(min γ (1 - γ) - d * η)) + 1 * L ^ (-(min γ (1 - γ) - d * η)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hexp_le (by positivity)) (by rw [one_mul]; exact hexp2)
    _ = _ := by ring

theorem smallGapPairAt {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) {η : ℝ} (hη : 0 ≤ η) {δ : ℝ}
    (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) {C1 : ℝ} (hC1 : 0 < C1) :
    ∃ K B R : ℝ, ∀ L ≥ R, SmallGapPairAt.{u, v} d L γ δ η C1 K B := by
  obtain ⟨C, L₀, hC, h⟩ := smallgap_count_bound d hd γ hγ η
  refine ⟨(8 * 9 ^ d * C * δ⁻¹ + 1) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 4, 8, max L₀ (Real.exp 1), fun L hL => ?_⟩
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hLL : L ≥ L₀ := (le_max_left _ _).trans hL
  have hl8 : Real.log L ^ (8 : ℝ) = Real.log L ^ 8 := by
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  intro V D _ _ _ M hcap hloop v₁ hv₁ v₂ hv₂ hne hbb h1 h2 hconnM hconnP P hP Adm hAdm
  have hdeg : ∀ v ∈ M.atoms, M.deg v ≤ 4 := fun v hv => by
    have h := hcap v hv
    have hsum := Mole.outdeg_add_indeg M v
    omega
  have hcount := h L hLL δ hδ M hcap hv₁ hv₂ hne h1 h2 hbb Adm (fun κ hκ => (hAdm κ hκ).2)
  have hmain := countAFree_le_erase_pair M hloop hdeg hne hv₁ hv₂ hconnM hconnP
    (erase_pair_nonempty M hloop hne (by omega)) (d := d) (η := η) (C1 := C1) hL1 hlog hδ.1 hC1 P hP Adm
    (fun κ hκ => (hAdm κ hκ).1) _ (r := 4) (by rw [h1, h2, hbb]; norm_num) hcount
  refine hmain.trans ?_
  rw [hl8]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hari := smallgap_arith hd hγ hη hL1 hC hδ.1
  have hb0 : 0 ≤ (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 4 := by have := hδ.1; positivity
  have hlog8 : (Real.log L ^ 2) ^ 4 = Real.log L ^ 8 := by ring
  rw [hlog8]
  calc ((⌈8 * ((2 * L + 1) ^ d * (2 * (L * L ^ (-γ + η)) + 1) ^ d * (C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))))⌉₊ : ℕ) : ℝ) *
        (L ^ (-((d : ℝ) - γ) * ((4 : ℕ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 4) * Real.log L ^ 8
      = (((⌈8 * ((2 * L + 1) ^ d * (2 * (L * L ^ (-γ + η)) + 1) ^ d * (C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))))⌉₊ : ℕ) : ℝ) *
        L ^ (-((d : ℝ) - γ) * ((4 : ℕ) : ℝ))) * ((C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 4 * Real.log L ^ 8) := by ring
    _ ≤ ((8 * 9 ^ d * C * δ⁻¹ + 1) * L ^ (-(min γ (1 - γ) - d * η))) * ((C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 4 * Real.log L ^ 8) :=
        mul_le_mul_of_nonneg_right hari (by positivity)
    _ = _ := by ring

/-- **`SmallGapPairInput`** (DH23 L1975), for `γ > 1/2` and `η > 0`. -/
theorem smallGapPairInput {d : ℕ} (hd : 3 ≤ d) (γ η : ℝ) (hγ1 : γ < 1) (hη : 0 ≤ η) :
    SmallGapPairInput.{u, v} d γ η := fun hγ =>
  ⟨1, le_rfl, fun C1 hC1 δ hδ => smallGapPairAt.{u, v} hd ⟨by linarith, hγ1⟩ hη hδ (by linarith)⟩

end WaveTurbulence.FinalCountG8
