/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPrefix
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGReg2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGate
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmPrefix`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY: the parameter prefix.**

* `finalCount_reg_half : WTPrefix (fun P => 1 / 2 < P.γ → FinalCountRegAt P)`: `η₀` from `d, γ` (the smallness conditions of
  `reg_garden_bound`), `C₁ = 4 Cstar(d, γ, η)`, the exponents `m, c` from `d` and `𝔇` (TARGET L2253: `R ≤ 10 R_{p+1}` and
  `|G| ≤ N_{p+1}^4` are powers of `log L`), and the threshold `L₀` of `reg_garden_bound`.
* `finalCountAtWith_largeConstantMonotone`, `prefix_mono`.
* `finalCount_half_of_low`: `FinalCountGateHalf` from the LOW half (`prefix_and` of the REG and LOW halves, `finalCountAt_of_reg_low`). 

**Low-range change (L6-HASM; PLAN-L6 §3d (ii) η-choice).** `finalCount_reg_half` → `finalCount_reg_low`
(`P.γ ≤ 1/2 →`; `η₀ = min (min γ (1−γ)/(1000 d)) (1/(4·1440061))`, the `(2γ−1)/(1000 d)` term deleted; `[Src.AsmInputs]`);
`finalCountAtWith_largeConstantMonotone` at `P.γ ≤ 1/2 →`; `finalCount_half_of_low` → `finalCount_low_of_low`
(conclusion: the γL gate body for `P.γ ≤ 1/2`, L6's `FinalCountLAt`). TriReal's `200η ≤ γ`, `200η ≤ 1 − γ` follow from
`dη ≤ min γ (1−γ)/1000`, `d ≥ 3`.-/
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

theorem finalCountAtWith_largeConstantMonotone (Φ : ∀ {R : ℕ}, Garden (2 * R) → Prop) :
    LargeConstantMonotone (fun P => P.γ ≤ 1 / 2 → FinalCountAtWith P Φ) := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h hγ p hp R hR hRmax G hplain hirred hbal hn hnmax D C hD hgeom hΦ base roots Adm hAdm
  rw [N_largeConstants] at hnmax
  rw [R_largeConstants] at hRmax
  have h0 := h hγ p hp R hR hRmax G hplain hirred hbal hn hnmax D C hD hgeom hΦ base roots Adm hAdm
  refine le_trans ?_ h0
  exact countA_mono_C₁ G.molecule P.L P.γ P.δ P.C₁ c₁ hδ.le (by linarith) h₁ base Adm C.ladderScale

/-- **The REG half of the amended gate, `0 < γ ≤ 1/2`.** -/
theorem finalCount_reg_low : WTPrefix (fun P => P.γ ≤ 1 / 2 → FinalCountRegAt P) := by
  intro d hd γ hγ
  by_cases hγh : γ ≤ 1 / 2
  swap
  · exact ⟨1, one_pos, fun η _ φin _ τ _ φ _ => ⟨1, le_rfl, 1, one_pos, fun ν _ => ⟨1, one_pos, fun δ _ D _ _ =>
      ⟨1, le_rfl, 2, le_rfl, fun L _ h => absurd h hγh⟩⟩⟩⟩
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hγ1 : γ < 1 := hγ.2
  set a1 : ℝ := min γ (1 - γ) / 1000 / d with ha1
  set a3 : ℝ := 1 / (4 * 1440061) with ha3
  have ha1p : 0 < a1 := by
    have : 0 < min γ (1 - γ) := lt_min hγ.1 (by linarith)
    positivity
  have ha3p : 0 < a3 := by positivity
  refine ⟨min a1 a3, lt_min ha1p ha3p, fun η hη φin _ τ _ φ _ => ?_⟩
  have hηa1 : η ≤ a1 := hη.2.trans (min_le_left _ _)
  have hηa3 : η ≤ a3 := hη.2.trans (min_le_right _ _)
  have hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000 := by
    have := mul_le_mul_of_nonneg_left hηa1 hdpos.le
    rwa [ha1, mul_div_cancel₀ _ hdpos.ne'] at this
  have hηs : 4 * 1440061 * η ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hηa3 (by norm_num : (0 : ℝ) ≤ 4 * 1440061)
    rwa [ha3, mul_one_div_cancel (by norm_num)] at this
  obtain ⟨Cs, hCs, hb⟩ := reg_garden_bound hd ⟨hγ.1, hγh⟩ hη.1 hsm hηs
  refine ⟨4 * Cs, by linarith, 1, one_pos, fun ν _ => ⟨1, one_pos, fun δ hδ D hD htime => ?_⟩⟩
  obtain ⟨R₀, hR₀, hR⟩ := hb (4 * (40 * d) ^ (2 * D + 2) + 1) ((40 * d) ^ (2 * D + 1) + 4) (4 * Cs) le_rfl δ
    ⟨hδ.1, hδ.2⟩
  refine ⟨1, le_rfl, max (max R₀ 2) (Real.exp 1), le_trans (le_max_right _ _) (le_max_left _ _), fun L hL _ => ?_⟩
  have hLR₀ : R₀ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLe : Real.exp 1 ≤ L := le_trans (le_max_right _ _) hL
  have hlog : 1 ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos 1) hLe
    rwa [Real.log_exp] at this
  intro p hp R hR1 hRm G hpl _ _ _ hnm D' C _ hg hregG base roots Adm hAdm
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
  exact hR L hLR₀ G hpl hR1 hRc hord D' C hg hregG base roots Adm hAdm

/-- **The low-range gate body over `γL` (`FinalCountAt`, i.e. L6's `FinalCountLAt`) from the LOW half.** -/
theorem finalCount_low_of_low (hlow : WTPrefix (fun P => P.γ ≤ 1 / 2 → FinalCountLowAt P)) :
    WTPrefix (fun P => P.γ ≤ 1 / 2 → FinalCountAt P) :=
  prefix_mono (prefix_and finalCount_reg_low hlow (finalCountAtWith_largeConstantMonotone _)
      (finalCountAtWith_largeConstantMonotone _))
    (fun P h hγ => finalCountAt_of_reg_low (h.1 hγ) (h.2 hγ))

end WaveTurbulence.GammaLow.FinalCount.H
