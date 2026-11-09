/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedCircuitRank
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedRawPrefactorLog
public import WaveTurbulence.Foundations.Spine.SplicedRawPrefactorLog
public import WaveTurbulence.Foundations.Spine.SplicedCountingAbsorption
/-! Normalize and absorb the source fixed-choice counting bound, including an arbitrary positive scale-choice cost. -/
public section
open WaveTurbulence.Induct
set_option autoImplicit false
-- Ported from main `Spine.SplicedChoiceScaleAbsorption` (sha256 b7b0a0aa534fc03a923d0dc86b352243ed32b4bc2708cc75b2bf9eb3392777dc) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}

theorem splicedRawPrefactor_mul_choiceScale_le {R d : ℕ} (G : Garden (2 * R))
    (C : CountingChoices γv G d) (hgeom : CountingGeometry G C)
    (hn : 1 ≤ G.order) (hR : 1 ≤ R)
    {L δ C₁ C₀ η ν scaleCost : ℝ} (hL : 1 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC₁ : 1 ≤ C₁) (hC₀ : 0 < C₀) (hscale : 0 < scaleCost)
    (ha : δ ^ (5 * ν) ≤ η ^ 6)
    (hb : Real.log scaleCost ≤ η ^ 6 * Real.log L)
    (hsmall : Real.log C₁ + Real.log C₀ + 5 * ν * Real.log δ ≤ 0) (γ : ℝ) :
    splicedRawPrefactor G C L γ η δ C₁ ν * C₀ ^ G.order *
      scaleCost ^ (G.molecule.rho + C.numCriticalSG) ≤
      C₁ * Real.exp (G.order * (Real.log C₁ - 10 * ν * Real.log δ) +
        (-η ^ 6 * (G.molecule.rho + C.subpro.hinges.card) -
          ((R : ℝ) - 1) * (1 / 4 + 1 / 50)) * Real.log L) := by
  have hL0 := zero_lt_one.trans hL
  have hC₁0 := zero_lt_one.trans_le hC₁
  have hlogL : 0 < Real.log L := Real.log_pos hL
  have hpref := splicedRawPrefactor_pos G C hL0 hδ hC₁0 γ η ν
  have hleft : 0 < splicedRawPrefactor G C L γ η δ C₁ ν * C₀ ^ G.order *
      scaleCost ^ (G.molecule.rho + C.numCriticalSG) := by positivity
  have hright : 0 < C₁ * Real.exp (G.order * (Real.log C₁ - 10 * ν * Real.log δ) +
        (-η ^ 6 * (G.molecule.rho + C.subpro.hinges.card) -
          ((R : ℝ) - 1) * (1 / 4 + 1 / 50)) * Real.log L) := by positivity
  apply (Real.log_le_log_iff hleft hright).mp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hpref.ne' (by positivity),
    Real.log_pow, Real.log_pow, Real.log_mul hC₁0.ne' (Real.exp_pos _).ne', Real.log_exp,
    log_splicedRawPrefactor G C hgeom hn hL0 hδ hC₁0 γ η ν]
  have hq : (C.subpro.hinges.card : ℝ) ≤ C.numCriticalSG := by exact_mod_cast hgeom.hinges_card_le
  have hh := spliced_counting_exponent_le (R := (R : ℝ)) (ρ := (G.molecule.rho : ℝ))
    (p := (C.numCriticalSG : ℝ)) (q := (C.subpro.hinges.card : ℝ)) (n := (G.order : ℝ))
    (Real.log_nonneg hC₁) (Real.log_nonpos hδ.le hδ1)
    hlogL.le (by positivity : 0 ≤ η ^ 6) (Nat.cast_nonneg G.order)
    (by exact_mod_cast hR) (Nat.cast_nonneg G.molecule.rho) (Nat.cast_nonneg C.numCriticalSG)
    hq ha hb hsmall
  have htwo : 0 ≤ (G.order : ℝ) * Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  push_cast
  linarith

end WaveTurbulence.GammaLow.Famc
