/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKStep.Pot
public import WaveTurbulence.Foundations.FinalCount.LowChain45

/-! # C1b2 MK-CHAIN (11): the numerics with survivors (`ll_numE`, `exists_NLE`, the `L^{2m}` factor)

- `exists_NLE`: main's `exists_NL` (LowChain45) with the extra node count `c_D⁴` of the re-cut nodes in the phase-1
  bound (C1b1's `phase1_coverLE_of_inputs`, four node families).
- `ll_numE`: main's `ll_num` (LowChain44) twice, for the D1 constant and for the re-cut constant `CR` of C1a's
  `Ex1RC` (same shape `Cs·ν·(1+δ⁻¹)²·(12/(η²−η³))¹²`).
- `WPot_g1_add`, `WPot_init_eqLE`, `init_exp_leE`: the survivor budget at the initial state. With
  `Fmax = 2R − 1 + m` and C1a's `WPot_g1E_le` (`W(Y, g1E) ≤ W(Y·L^m, g1)`), the initial potential is main's times
  `L^{m}·L^{γ₀ m} ≤ L^{2m}` (`γ₀ = min γ (1−γ) ≤ 1`). -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)
open scoped ENNReal
namespace WaveTurbulence.Flower.FinalMKChain
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep WaveTurbulence.LGSpine.SourceVine

universe u
variable {d : ℕ}

/-- The phase-1 node count with the re-cut nodes (main's `nat_poly_auxL`, first bound, plus `c_D⁴`). -/
theorem nat_poly_auxLE (t : ℕ) (ht : 1 ≤ t) (x y z : ℕ) (hx : x ≤ t) (hy : y ≤ t) (hz : z ≤ t) :
    (y * (y * (y * (y * (z * (2 * (x * 2))))))) + x * (y * (y * (z * (2 * (x * 2))))) + y * (y * (y * y)) +
      y * (y * (y * y)) + 1 ≤ 4096 * t ^ 13 := by
  have p : ∀ k, k ≤ 13 → t ^ k ≤ t ^ 13 := fun k hk => Nat.pow_le_pow_right ht hk
  have h1 : (y * (y * (y * (y * (z * (2 * (x * 2))))))) + x * (y * (y * (z * (2 * (x * 2))))) + y * (y * (y * y)) +
      y * (y * (y * y)) + 1 ≤
      t * (t * (t * (t * (t * (2 * (t * 2)))))) + t * (t * (t * (t * (2 * (t * 2))))) + t * (t * (t * t)) +
        t * (t * (t * t)) + 1 := by gcongr
  have e1 : t * (t * (t * (t * (t * (2 * (t * 2)))))) + t * (t * (t * (t * (2 * (t * 2))))) + t * (t * (t * t)) +
      t * (t * (t * t)) + 1 = 4 * t ^ 6 + 4 * t ^ 5 + 2 * t ^ 4 + 1 := by ring
  have q := p 0 (by omega)
  have q4 := p 4 (by omega)
  have q5 := p 5 (by omega)
  have q6 := p 6 (by omega)
  simp only [pow_zero] at q
  omega

/-- **The node count `N`** (main's `exists_NL`, LowChain45, with the re-cut nodes in the phase-1 bound). -/
theorem exists_NLE (a cD m : ℕ) {L : ℝ} (hL : Real.exp 1 ≤ L) (ha : ((2 * a : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m)
    (hc : cD ≤ 4 * a) :
    ∃ N : ℕ,
      (cD * (cD * (cD * (cD * ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * a) * 2))))))) +
        (2 * a) * (cD * (cD * ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * a) * 2))))) + cD * (cD * (cD * cD)) +
        cD * (cD * (cD * cD)) + 1 ≤ N ∧
      nodeBound2 (2 * a) cD ⌈2 * Real.log L⌉₊ + 1 ≤ N ∧
      (2 * a) * (cD * (cD * ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * a) * 2))))) + 1 ≤ N ∧
      2 * a * cD * cD + 1 ≤ N ∧
      (N : ℝ) ≤ 4096 * (2 * (1 + Real.log L) ^ (m + 1)) ^ 13 := by
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) hL
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hB1 : 1 ≤ 1 + Real.log L := by linarith
  set ℓ : ℕ := ⌈2 * Real.log L⌉₊ + 1 with hℓ
  set t : ℕ := max (2 * a) (max cD ℓ) with ht
  have ht1 : 1 ≤ t := le_trans (by omega : 1 ≤ ℓ) (le_trans (le_max_right _ _) (le_max_right _ _))
  have h1 := nat_poly_auxLE t ht1 (2 * a) cD ℓ (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_right _ _) (le_max_right _ _))
  obtain ⟨-, -, h3, h4⟩ := nat_poly_auxL t ht1 (2 * a) cD ℓ (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) (le_max_right _ _))
  obtain ⟨-, h2, -, -⟩ := nat_poly_auxL t ht1 (2 * a) cD ⌈2 * Real.log L⌉₊ (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (by omega : ⌈2 * Real.log L⌉₊ ≤ ℓ) (le_trans (le_max_right _ _) (le_max_right _ _)))
  refine ⟨4096 * t ^ 13, h1, h2, h3, h4, ?_⟩
  set T : ℝ := 2 * (1 + Real.log L) ^ (m + 1) with hT
  have hBm : (1 + Real.log L) ^ m ≤ (1 + Real.log L) ^ (m + 1) := pow_le_pow_right₀ hB1 (by omega)
  have hBm1 : 1 ≤ (1 + Real.log L) ^ (m + 1) := one_le_pow₀ hB1
  have htT : (t : ℝ) ≤ T := by
    have e1 : ((2 * a : ℕ) : ℝ) ≤ T := by rw [hT]; linarith
    have e2 : (cD : ℝ) ≤ T := by
      have : (cD : ℝ) ≤ ((4 * a : ℕ) : ℝ) := by exact_mod_cast hc
      push_cast at this e1 ha ⊢; rw [hT]; linarith
    have e3 : (ℓ : ℝ) ≤ T := by
      have h1 : (⌈2 * Real.log L⌉₊ : ℝ) < 2 * Real.log L + 1 := Nat.ceil_lt_add_one (by linarith)
      have h2 : 1 + Real.log L ≤ (1 + Real.log L) ^ (m + 1) := by
        simpa using pow_le_pow_right₀ hB1 (show 1 ≤ m + 1 by omega)
      rw [hℓ]; push_cast; rw [hT]; linarith
    have : (t : ℝ) = max ((2 * a : ℕ) : ℝ) (max (cD : ℝ) (ℓ : ℝ)) := by rw [ht]; push_cast; rfl
    rw [this]; exact max_le e1 (max_le e2 e3)
  push_cast
  gcongr

/-- **`ll_num` with survivors**: main's numerics (LowChain44) for the D1 constant and for C1a's re-cut constant `CR`
(the same shape), at a common threshold. -/
theorem ll_numE {γ η : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η) (hη40 : η ≤ 1 / 40) {CsA CsN CsD CsR : ℝ}
    (hCsA : 0 ≤ CsA) (hCsN : 0 ≤ CsN) (hCsD : 0 ≤ CsD) (hCsR : 0 ≤ CsR) (m : ℕ) {δ : ℝ} (hδ : δ ∈ Ioc (0 : ℝ) 1) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
      LLNum d γ η δ L m ((CsA * (2 ^ d * ((13 : ℝ) / (2 * η - η ^ 3)) ^ 13)) * (1 + δ⁻¹))
        (CsN * (1 + Real.log L) ^ m * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8))
        (CsD * (1 + Real.log L) ^ m * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8)) ∧
      LLNum d γ η δ L m ((CsA * (2 ^ d * ((13 : ℝ) / (2 * η - η ^ 3)) ^ 13)) * (1 + δ⁻¹))
        (CsN * (1 + Real.log L) ^ m * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8))
        (CsR * (1 + Real.log L) ^ m * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8)) := by
  obtain ⟨R₁, hR₁, h₁⟩ := ll_num (d := d) hγ0 hγ1 hη hη40 hCsA hCsN hCsD m hδ
  obtain ⟨R₂, hR₂, h₂⟩ := ll_num (d := d) hγ0 hγ1 hη hη40 hCsA hCsN hCsR m hδ
  exact ⟨max R₁ R₂, le_trans hR₁ (le_max_left _ _), fun L hL =>
    ⟨h₁ L (le_trans (le_max_left _ _) hL), h₂ L (le_trans (le_max_right _ _) hL)⟩⟩

section pot
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]

/-- Raising `Fmax` by `x` multiplies the phase-1 potential by `L^{γ₀ x}`. -/
theorem WPot_g1_add {L γ η : ℝ} (hL : 0 < L) (Y : ℝ) (crit : V → Prop) (F x : ℝ) (h : HSt V D₀) :
    WPot L γ η Y (g1 γ η crit (F + x)) h = WPot L γ η (Y * L ^ (min γ (1 - γ) * x)) (g1 γ η crit F) h := by
  have e : Y * L ^ (-g1 γ η crit (F + x) h) = Y * L ^ (min γ (1 - γ) * x) * L ^ (-g1 γ η crit F h) := by
    rw [mul_assoc, ← Real.rpow_add hL]; congr 2; unfold g1; ring
  show ENNReal.ofReal (potR L γ η (Y * L ^ (-g1 γ η crit (F + x) h)) h) =
    ENNReal.ofReal (potR L γ η (Y * L ^ (min γ (1 - γ) * x) * L ^ (-g1 γ η crit F h)) h)
  rw [e]

/-- **The initial potential with the survivor budget** (main's `WPot_init_eqL` with `g1E`, `Fmax = 2R − 1 + m`):
at most main's value times `L^{m + γ₀ m}`. -/
theorem WPot_init_eqLE {Rn R : ℕ} {M₀ : Molecule V D₀} (hS : SubHypL Rn M₀) {L γ η ε0 c : ℝ} (hc : 0 ≤ c)
    (hL1 : 1 ≤ L) (crit : V → Prop) {m : ℕ} (E : Fin m → Object M₀) :
    WPot L γ η (c * L ^ (eraseA γ η * (R : ℝ) + 4 * η * ((R : ℝ) - 1) - ε0))
        (g1E γ η crit (2 * (R : ℝ) - 1 + m) E) (HSt.init M₀) ≤
      ENNReal.ofReal (c * L ^ ((m : ℝ) + min γ (1 - γ) * m)) *
        ENNReal.ofReal (L ^ ((R - 1 : ℝ) * (eraseA γ η + 2 * min γ (1 - γ) + 4 * η) - ε0 -
          4 * η ^ 6 * ((M₀.rho : ℝ) + ((M₀.atoms.filter crit).card : ℝ)))) := by
  have hL : 0 < L := by linarith
  have hap : 0 < apProd L γ η (HSt.init M₀).s := by
    have e3 : apProd L γ η (HSt.init M₀).s = 1 := apProd_init L γ η M₀
    rw [e3]; norm_num
  have hY : 0 ≤ c * L ^ (eraseA γ η * (R : ℝ) + 4 * η * ((R : ℝ) - 1) - ε0) := by positivity
  refine (WPot_g1E_le hL1 hY crit _ E hap).trans (le_of_eq ?_)
  rw [WPot_g1_add hL]
  have e : c * L ^ (eraseA γ η * (R : ℝ) + 4 * η * ((R : ℝ) - 1) - ε0) * L ^ (m : ℝ) * L ^ (min γ (1 - γ) * m) =
      c * L ^ ((m : ℝ) + min γ (1 - γ) * m) * L ^ (eraseA γ η * (R : ℝ) + 4 * η * ((R : ℝ) - 1) - ε0) := by
    rw [Real.rpow_add hL]; ring
  rw [e]
  exact WPot_init_eqL hS (by positivity) hL crit

/-- Real arithmetic of the initial state with survivors (main's `init_exp_le` times `L^{m + γ₀ m} ≤ L^{2m}`). -/
theorem init_exp_leE (hd : 3 ≤ d) {γ η : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη0 : 0 < η) (hη : η ≤ 1 / 40) {R S : ℝ}
    (hR : 1 ≤ R) {L : ℝ} (hL : 1 ≤ L) {N4 : ℝ} (hN0 : 0 ≤ N4) (hN4 : N4 ≤ L ^ ((η ^ 5 - 4 * η ^ 6) / 4)) (m : ℕ) :
    N4 * (L ^ ((m : ℝ) + min γ (1 - γ) * m) *
        L ^ ((R - 1) * (eraseA γ η + 2 * min γ (1 - γ) + 4 * η) - (η ^ 5 - 4 * η ^ 6) / 2 - 4 * η ^ 6 * S)) ≤
      L ^ (2 * (m : ℝ)) * L ^ (-4 * η ^ 6 * S) *
        L ^ ((R - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20) - (η ^ 5 - 4 * η ^ 6) / 4) := by
  have hL0 : 0 < L := by linarith
  have hmain := init_exp_le hd hγ0 hγ1 hη0 hη hR hL hN4 (S := S)
  have hγm : min γ (1 - γ) ≤ 1 := le_trans (min_le_left _ _) hγ1.le
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hpow : L ^ ((m : ℝ) + min γ (1 - γ) * m) ≤ L ^ (2 * (m : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hL (by nlinarith)
  calc N4 * (L ^ ((m : ℝ) + min γ (1 - γ) * m) *
        L ^ ((R - 1) * (eraseA γ η + 2 * min γ (1 - γ) + 4 * η) - (η ^ 5 - 4 * η ^ 6) / 2 - 4 * η ^ 6 * S))
      = L ^ ((m : ℝ) + min γ (1 - γ) * m) *
        (N4 * L ^ ((R - 1) * (eraseA γ η + 2 * min γ (1 - γ) + 4 * η) - (η ^ 5 - 4 * η ^ 6) / 2 -
          4 * η ^ 6 * S)) := by ring
    _ ≤ L ^ (2 * (m : ℝ)) * (L ^ (-4 * η ^ 6 * S) *
        L ^ ((R - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20) - (η ^ 5 - 4 * η ^ 6) / 4)) := by
        gcongr
    _ = _ := by ring

end pot

end WaveTurbulence.Flower.FinalMKChain
