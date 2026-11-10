/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowIface
public import WaveTurbulence.Foundations.FinalCount.AsmPrefix
/-! **FINALCOUNT-ASSEMBLY (LOW-GLUE, session 20): the parameter prefix of the LOW half.**

`finalCount_low_half_of_garden : LowGardenBoundAll → WTPrefix (fun P => 1/2 < P.γ → FinalCountLowAt P)` is `finalCount_reg_half`
with the garden-level REG bound replaced by the LOW one (`η₀` from `LowGardenBoundAll`, `C₁ = 4 Cstar`, the exponents `m, c` from `d`
and `𝔇`, the threshold `L₀` of the garden bound).  `finalCount_half_of_lowGarden` closes `FinalCountGateHalf` with
`finalCount_half_of_low`.  These are conditional helpers (distinct names); the LOW-GARDEN packet proves `LowGardenBoundAll`. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open Set (Ioo Ioc)
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

/-- **The LOW half of the amended gate, from the garden-level LOW bound.** -/
theorem finalCount_low_half_of_garden (hlow : LowGardenBoundAll) :
    WTPrefix (fun P => 1 / 2 < P.γ → FinalCountLowAt P) := by
  intro d hd γ hγ
  by_cases hγh : 1 / 2 < γ
  swap
  · exact ⟨1, one_pos, fun η _ φin _ τ _ φ _ => ⟨1, le_rfl, 1, one_pos, fun ν _ => ⟨1, one_pos, fun δ _ D _ _ =>
      ⟨1, le_rfl, 2, le_rfl, fun L _ h => absurd h hγh⟩⟩⟩⟩
  obtain ⟨η₀, hη₀, hall⟩ := hlow d hd γ hγh hγ.2
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

end WaveTurbulence.FinalCountAsm
