/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTopInit
public import WaveTurbulence.Foundations.FinalCount.AsmTerm16c
public import WaveTurbulence.Foundations.FinalCount.AsmMaxGap2
public import WaveTurbulence.Foundations.FinalCount.AsmEx1
public import WaveTurbulenceVineParam.VineParamMain
/-! **FINALCOUNT-ASSEMBLY (top level): the class theorem `reg_class_bound`.**  For a molecule `M₀` with the standing hypotheses (`SubHyp`, class
hypotheses of `hterm_main`, `hmem`, `hend`), at base `0`: `𝔄(M₀; A0) ≤ L^{-4η⁶(ρ+crit)} L^{(R-1)(d-γ-1/4-1/40-1/20) - (η⁵-4η⁶)/4}`.
Quantifiers as in `WTPrefix`: `Cstar` depends only on `d, γ, η`; `m` enters only through the threshold `R₀`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountG8
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

/-- Real arithmetic of the initial state. -/
theorem init_exp_le {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη0 : 0 < η) (hη : η ≤ 1 / 40) {R S : ℝ} (hR : 1 ≤ R)
    {L : ℝ} (hL : 1 ≤ L) {N4 : ℝ} (hN4 : N4 ≤ L ^ ((η ^ 5 - 4 * η ^ 6) / 4)) :
    N4 * L ^ ((R - 1) * (eraseA γ η + 2 * min γ (1 - γ) + 4 * η) - (η ^ 5 - 4 * η ^ 6) / 2 - 4 * η ^ 6 * S) ≤
      L ^ (-4 * η ^ 6 * S) * L ^ ((R - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20) - (η ^ 5 - 4 * η ^ 6) / 4) := by
  have hL0 : 0 < L := by linarith
  have hslack := d_gamma_slack (d : ℝ) γ (by exact_mod_cast hd) hγ0 hγ1
  have hg : eraseA γ η + 2 * min γ (1 - γ) + 4 * η ≤ (d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20 := by
    unfold eraseA gam0; nlinarith [hslack]
  have h1 : (R - 1) * (eraseA γ η + 2 * min γ (1 - γ) + 4 * η) ≤ (R - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20) :=
    mul_le_mul_of_nonneg_left hg (by linarith)
  calc N4 * L ^ ((R - 1) * (eraseA γ η + 2 * min γ (1 - γ) + 4 * η) - (η ^ 5 - 4 * η ^ 6) / 2 - 4 * η ^ 6 * S)
      ≤ L ^ ((η ^ 5 - 4 * η ^ 6) / 4) * L ^ ((R - 1) * (eraseA γ η + 2 * min γ (1 - γ) + 4 * η) - (η ^ 5 - 4 * η ^ 6) / 2 - 4 * η ^ 6 * S) := by
        gcongr
    _ = L ^ (-4 * η ^ 6 * S) * L ^ ((R - 1) * (eraseA γ η + 2 * min γ (1 - γ) + 4 * η) - (η ^ 5 - 4 * η ^ 6) / 4) := by
        rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; congr 1; ring
    _ ≤ L ^ (-4 * η ^ 6 * S) * L ^ ((R - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20) - (η ^ 5 - 4 * η ^ 6) / 4) := by
        gcongr

end WaveTurbulence.FinalCountAsm
