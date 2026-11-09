/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowGlue
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPrefix
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowIface
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SpineInputsV2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowGlue`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (LOW-GLUE, session 20): the parameter prefix of the LOW half.**

`finalCount_low_half_of_garden : LowGardenBoundAll → WTPrefix (fun P => 1/2 < P.γ → FinalCountLowAt P)` is `finalCount_reg_half`
with the garden-level REG bound replaced by the LOW one (`η₀` from `LowGardenBoundAll`, `C₁ = 4 Cstar`, the exponents `m, c` from `d`
and `𝔇`, the threshold `L₀` of the garden bound).  `finalCount_half_of_lowGarden` closes `FinalCountGateHalf` with
`finalCount_half_of_low`.  These are conditional helpers (distinct names); the LOW-GARDEN packet proves `LowGardenBoundAll`.

**Low-range change (L6-HLOW; PLAN-L6 §3f rule 4, H-MS2's restated row 6).** `finalCount_low_half_of_garden` concludes
`WTPrefix (fun P => P.γ ≤ 1/2 → FinalCountLowAt P)` (main: `1/2 < P.γ`), from the low-range `LowGardenBoundAll`
(`0 < γ → γ ≤ 1/2`, LowIface); `finalCount_half_of_lowGarden` closes H-MS2's `FinalCountGateHalf`
(`WTPrefix fun P => P.γ ≤ 1/2 → FinalCountAt P`) with H-ASM's `finalCount_low_of_low` (main: `finalCount_half_of_low`). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open Set (Ioo Ioc)
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

/-- **The LOW half of the amended gate, from the garden-level LOW bound.** -/
theorem finalCount_low_half_of_garden (hlow : LowGardenBoundAll) :
    WTPrefix (fun P => P.γ ≤ 1 / 2 → FinalCountLowAt P) := by
  intro d hd γ hγ
  by_cases hγh : γ ≤ 1 / 2
  swap
  · exact ⟨1, one_pos, fun η _ φin _ τ _ φ _ => ⟨1, le_rfl, 1, one_pos, fun ν _ => ⟨1, one_pos, fun δ _ D _ _ =>
      ⟨1, le_rfl, 2, le_rfl, fun L _ h => absurd h hγh⟩⟩⟩⟩
  obtain ⟨η₀, hη₀, hall⟩ := hlow d hd γ hγ.1 hγh
  refine ⟨η₀, hη₀, fun η hη φin _ τ _ φ _ => ?_⟩
  obtain ⟨Cs, hCs, hb⟩ := hall η hη.1 hη.2
  refine ⟨4 * Cs, by linarith, 1, one_pos, fun ν _ => ⟨1, one_pos, fun δ hδ D hD htime => ?_⟩⟩
  obtain ⟨R₀, hR₀, hR⟩ := hb (4 * (40 * d) ^ (2 * D + 2) + 1) ((40 * d) ^ (2 * D + 1) + 4) (4 * Cs) le_rfl δ
    ⟨hδ.1, hδ.2⟩
  refine ⟨1, le_rfl, max (max R₀ 2) (Real.exp 1), le_trans (le_max_right _ _) (le_max_left _ _), fun L hL _ => ?_⟩
  have hLR₀ : R₀ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLe : Real.exp 1 ≤ L := le_trans (le_max_right _ _) hL
  have hlog : 1 ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos 1) hLe
    rwa [Real.log_exp] at this
  intro p hp R hR1 hRm G hpl hirr hbal hn hnm D' C hh hg hlowG base roots Adm hAdm
  -- `R ≤ (1 + log L)^c`
  have hRc : (R : ℝ) ≤ (1 + Real.log L) ^ ((40 * d) ^ (2 * D + 1) + 4) := by
    have h2 := Rdown_le_log_pow ⟨d, γ, η, φin, τ, φ, 4 * Cs, ν, δ, D, 1, L⟩ (D - (p + 1))
    have hexp : (40 * d) ^ (2 * (D - (p + 1)) + 1) ≤ (40 * d) ^ (2 * D + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : (WTParams.Rdown ⟨d, γ, η, φin, τ, φ, 4 * Cs, ν, δ, D, 1, L⟩ (D - (p + 1)) : ℝ) ≤
        Real.log L ^ ((40 * d) ^ (2 * D + 1)) :=
      le_trans h2 (pow_le_pow_right₀ hlog hexp)
    have h3 : (R : ℝ) ≤ 10 * (WTParams.Rdown ⟨d, γ, η, φin, τ, φ, 4 * Cs, ν, δ, D, 1, L⟩ (D - (p + 1)) : ℝ) := by
      exact_mod_cast hRm
    have h4 := ten_mul_pow_le hlog ((40 * d) ^ (2 * D + 1))
    nlinarith
  -- `2 |G| ≤ (1 + log L)^m`
  have hord : ((2 * G.order : ℕ) : ℝ) ≤ (1 + Real.log L) ^ (4 * (40 * d) ^ (2 * D + 2) + 1) := by
    have h1 := N_quartic_le_log_pow ⟨d, γ, η, φin, τ, φ, 4 * Cs, ν, δ, D, 1, L⟩ (by show 1 ≤ d; omega) hlog (p + 1)
    have h2 : (G.order : ℝ) ≤ (WTParams.N ⟨d, γ, η, φin, τ, φ, 4 * Cs, ν, δ, D, 1, L⟩ (p + 1) : ℝ) ^ 4 := by
      exact_mod_cast hnm
    have h3 := two_mul_pow_le hlog (4 * (40 * d) ^ (2 * D + 2))
    have h5 : (G.order : ℝ) ≤ Real.log L ^ (4 * (40 * d) ^ (2 * D + 2)) := h2.trans h1
    push_cast
    nlinarith
  exact hR L hLR₀ G hpl hirr hbal hn hR1 hRc hord D' C hh hg hlowG base roots Adm hAdm

/-- **`FinalCountGateHalf` from the garden-level LOW bound.** -/
theorem finalCount_half_of_lowGarden (hlow : LowGardenBoundAll) : FinalCountGateHalf :=
  finalCount_low_of_low (finalCount_low_half_of_garden hlow)

end WaveTurbulence.GammaLow.FinalCount.H
