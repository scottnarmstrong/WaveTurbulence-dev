/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.AkBridgeDefinitions
public import WaveTurbulence.Foundations.NLS.BridgeReduction
public import WaveTurbulence.Foundations.NLS.BridgeMeasurability

/-!
# Exact snapshot-5 NLS bridge

The declaration type below is copied byte-for-byte from the approved
pre-freeze snapshot; no draft theorem is imported.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

universe u

namespace WaveTurbulence.NLSBridge

theorem nlsAkBridge {d : ℕ} (hd : 1 ≤ d) (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (D : ℕ)
    (hD : 1 ≤ D) (α T : ℝ) (hα : α = L ^ (-γ)) (hT : T = D * δ * kineticTime α) :
    -- (1) forward
    (∀ (c : (Fin d → ℤ) → ℂ) (u : ℝ → (Fin d → ℝ) → ℂ), IsSmoothNLSSolution L α T c u →
      let M : ℝ := (L ^ d)⁻¹ * ∑' n, ‖c n‖ ^ 2
      let a : ℝ → (Fin d → ℤ) → ℂ := fun t n =>
        Complex.exp (-(Real.pi * δ * L ^ (2 * γ) * ‖latticePoint L n‖ ^ 2 * t : ℝ) *
          Complex.I) *
        Complex.exp (-(2 * α * M * δ * kineticTime α * t : ℝ) * Complex.I) *
        torusFourierCoeff L (u (δ * kineticTime α * t)) n
      IsASolution L γ δ D c a ∧ (∀ Λ : ℝ, ZNormOn L Λ (Icc 0 D) a < ⊤) ∧
        ∀ t ∈ Icc (0 : ℝ) D, ∀ n,
          ‖a t n‖ = ‖torusFourierCoeff L (u (δ * kineticTime α * t)) n‖) ∧
    -- (2) backward
    (∀ (c : (Fin d → ℤ) → ℂ) (a : ℝ → (Fin d → ℤ) → ℂ),
      (∀ s : ℝ, ∃ C, ∀ n, jbr (latticePoint L n) ^ s * ‖c n‖ ≤ C) →
      IsASolution L γ δ D c a →
      ∃ u : ℝ → (Fin d → ℝ) → ℂ, IsSmoothNLSSolution L α T c u ∧
        ∀ t ∈ Icc 0 T, ∀ n, ‖torusFourierCoeff L (u t) n‖ = ‖a (t / (δ * kineticTime α)) n‖) ∧
    -- (3) uniqueness
    (∀ (c : (Fin d → ℤ) → ℂ) (u u' : ℝ → (Fin d → ℝ) → ℂ),
      IsSmoothNLSSolution L α T c u → IsSmoothNLSSolution L α T c u' → ∀ t ∈ Icc 0 T, u t = u' t) ∧
    -- (4) measurability
    (∀ (Ω : Type u) [MeasurableSpace Ω] (c : Ω → (Fin d → ℤ) → ℂ), Measurable c →
      MeasurableSet {ω | ∃ v, IsSmoothNLSSolution L α T (c ω) v} ∧
      ∀ U : Ω → ℝ → (Fin d → ℝ) → ℂ,
        (∀ ω, (∃ v, IsSmoothNLSSolution L α T (c ω) v) → IsSmoothNLSSolution L α T (c ω) (U ω)) →
        ∀ t ∈ Icc 0 T, ∀ n, Measurable fun ω =>
          {ω | ∃ v, IsSmoothNLSSolution L α T (c ω) v}.indicator
            (fun ω => ‖torusFourierCoeff L (U ω t) n‖ ^ 2) ω) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  subst α
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have htime : T = δ * kineticTime (L ^ (-γ)) * D := by rw [hT]; ring
  have hTpos : 0 < T := by
    rw [htime]
    exact mul_pos (mul_pos hδ (NLS.kineticTime_rpow_neg_pos hL γ)) hDpos
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c u hu
    have hsol := hu.isAkSolution hL hδ.le htime
    have hnorm (Λ : ℝ) : ZNormOn L Λ (Icc 0 (D : ℝ)) (NLS.reducedCoeff L γ δ u) < ⊤ :=
      zNormOn_lt_top (NLS.bridge_uniform_weight_bound hL
        (fun N => hu.exists_uniform_decay_reducedCoeff hL hδ.le htime N) Λ)
    have H : IsASolution L γ δ D c (NLS.reducedCoeff L γ δ u) ∧
        (∀ Λ : ℝ, ZNormOn L Λ (Icc 0 D) (NLS.reducedCoeff L γ δ u) < ⊤) ∧
        ∀ t ∈ Icc (0 : ℝ) D, ∀ n, ‖NLS.reducedCoeff L γ δ u t n‖ =
          ‖torusFourierCoeff L (u (δ * kineticTime (L ^ (-γ)) * t)) n‖ :=
      ⟨(isASolution_iff_nls _ _ _ _ _ _).2 hsol, hnorm,
        fun t _ n => NLS.norm_reducedCoeff L γ δ u t n⟩
    rw [NLS.bridge_reducedCoeff_eq hL hTpos.le rfl hu] at H
    exact H
  · intro c a hc ha
    have H := NLS.IsAkSolution.isSmoothNLSSolution hL hδ hDpos htime
      (isRapidDecay_of_draft hL hc) ((isASolution_iff_nls _ _ _ _ _ _).1 ha)
    exact ⟨NLS.backSolution L γ δ c a, H⟩
  · intro c u u' hu hu' t ht
    exact hu.eq_of_eq hL hu' ht
  · intro Ω _ c hc
    refine ⟨NLS.bridge_measurableSet_solvable hL hTpos rfl hc, ?_⟩
    intro U hU t ht n
    exact NLS.bridge_measurable_indicator_energy hL hTpos rfl hc U hU ht n

end WaveTurbulence.NLSBridge
