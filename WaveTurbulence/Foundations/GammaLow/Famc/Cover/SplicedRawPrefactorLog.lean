/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SplicedCircuitRank
public import WaveTurbulence.Foundations.Spine.CountNormalizationLog
public import WaveTurbulence.Foundations.Spine.SplicedCircuitRank
/-! Exact logarithmic form of the literal selected-kernel count/Fourier prefactor. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
-- Ported from main `Spine.SplicedRawPrefactorLog` (sha256 c95f7793120539ab036d0c71cae8bcaf26ad9ba849b46e8ec6fba888b95ca274) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}

noncomputable def splicedRawPrefactor {R d : ℕ} (G : Garden (2 * R))
    (C : CountingChoices γv G d) (L γ η δ C₁ ν : ℝ) : ℝ :=
  (coupling d L γ δ) ^ G.order *
    (C₁ * (C₁ * δ ^ (-1 / 2 - 5 * ν)) ^ G.order * L ^ (δ ^ (5 * ν) * G.molecule.rho)) *
    ((L ^ (-4 * η ^ 6 * (G.molecule.rho + C.numCriticalSG)) *
      L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40))) /
      molecularCountNormalization G.molecule d L γ δ C₁)

theorem splicedRawPrefactor_pos {R d : ℕ} (G : Garden (2 * R))
    (C : CountingChoices γv G d) {L δ C₁ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hC₁ : 0 < C₁) (γ η ν : ℝ) : 0 < splicedRawPrefactor G C L γ η δ C₁ ν := by
  have ht := molecularCountNormalization_pos G.molecule d hL hδ hC₁ γ
  unfold splicedRawPrefactor coupling
  positivity

theorem log_splicedRawPrefactor {R d : ℕ} (G : Garden (2 * R))
    (C : CountingChoices γv G d) (hgeom : CountingGeometry G C)
    (hn : 1 ≤ G.order) {L δ C₁ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hC₁ : 0 < C₁)
    (γ η ν : ℝ) :
    Real.log (splicedRawPrefactor G C L γ η δ C₁ ν) =
      Real.log C₁ + G.order * (2 * Real.log C₁ - 5 * ν * Real.log δ - Real.log 2) +
        ((R : ℝ) - 1) * (Real.log δ / 2 - Real.log C₁) +
        (-4 * η ^ 6 * (G.molecule.rho + C.numCriticalSG) + δ ^ (5 * ν) * G.molecule.rho -
          ((R : ℝ) - 1) * (1 / 4 + 1 / 40)) * Real.log L := by
  have ht := molecularCountNormalization_pos G.molecule d hL hδ hC₁ γ
  have hc : 0 < coupling d L γ δ := by unfold coupling; positivity
  unfold splicedRawPrefactor
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_mul hC₁.ne' (Real.rpow_pos_of_pos hδ _).ne',
    Real.log_rpow hδ, Real.log_rpow hL, Real.log_div (by positivity) ht.ne',
    Real.log_mul (by positivity) (by positivity), Real.log_rpow hL, Real.log_rpow hL,
    log_molecularCountNormalization G.molecule d hL hδ hC₁ γ]
  unfold coupling
  rw [Real.log_div hδ.ne' (by positivity), Real.log_mul (by norm_num) (by positivity), Real.log_rpow hL]
  rw [spliced_circuitRank G C hgeom hn]
  push_cast
  ring

end WaveTurbulence.GammaLow.Famc
