/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SplicedRawPrefactorLog
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceFinalCountInputs
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedCircuitRank
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SplicedRawPrefactorLog`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Exact logarithmic form of the literal selected-kernel count/Fourier prefactor. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine

noncomputable def splicedRawPrefactor {R d : ℕ} (G : Garden (2 * R))
    (C : Src.CountingChoices Src.γL G d) (L γ η δ C₁ ν : ℝ) : ℝ :=
  (coupling d L γ δ) ^ G.order *
    (C₁ * (C₁ * δ ^ (-1 / 2 - 5 * ν)) ^ G.order * L ^ (δ ^ (5 * ν) * G.molecule.rho)) *
    ((L ^ (-4 * η ^ 6 * (G.molecule.rho + C.numCriticalSG)) *
      L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40))) /
      molecularCountNormalization G.molecule d L γ δ C₁)

theorem splicedRawPrefactor_pos {R d : ℕ} (G : Garden (2 * R))
    (C : Src.CountingChoices Src.γL G d) {L δ C₁ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hC₁ : 0 < C₁) (γ η ν : ℝ) : 0 < splicedRawPrefactor G C L γ η δ C₁ ν := by
  have ht := molecularCountNormalization_pos G.molecule d hL hδ hC₁ γ
  unfold splicedRawPrefactor coupling
  positivity

theorem log_splicedRawPrefactor {R d : ℕ} (G : Garden (2 * R))
    (C : Src.CountingChoices Src.γL G d) (hgeom : Src.CountingGeometry G C)
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

end WaveTurbulence.GammaLow.FinalCount.H
