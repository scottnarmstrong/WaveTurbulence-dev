/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Glue.Layergarden
public import WaveTurbulence.Foundations.GammaLow.Glue.Flower
public import WaveTurbulence.Foundations.XChain.V2Chain.FixedpointS
public import WaveTurbulence.Foundations.XChain.X2EDraft.OX2Exp
public import WaveTurbulence.Frozen.Theorems.WkeTaylor
public import Mathlib
public import WaveTurbulence.Frozen.Defs.ATr
public import WaveTurbulence.Frozen.Defs.AnsatzAt
public import WaveTurbulence.Frozen.Defs.IsGaussianData
public import WaveTurbulence.Frozen.Defs.IsSymmetricEvent
public import WaveTurbulence.Frozen.Defs.Jbr
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Lop
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsLambda
public import WaveTurbulence.Frozen.Defs.WTParamsN
public import WaveTurbulence.Frozen.Defs.WTPrefix
public import WaveTurbulence.Frozen.Defs.ZNorm
public import WaveTurbulence.Frozen.Defs.ZSpace

/-! # L0 GLUE: `fixedpoint` (v1) from FL-low and LG-low

Provider skeleton (conditional helper, distinct name). `V2Chain.fixedpointS_of_parts` at `S = univ` (as main's
`V2Chain.fixedpoint_v2_of_closed_gates_v3`, with `ofFull` in place of `ofR`/`toR`) from `layergardenFlower_v4`
(`layergardenFlower_v4_of_low`), `layergarden` (`layergarden_of_low`) and the sealed `wkeTaylor`, with the closed
inputs `Cpl.oX3Cpl`, `X2E.oX2Exp`. Its conclusion is the type of the frozen DRAFT_SORRY anchor
`WaveTurbulence.fixedpoint` (`Frozen/Theorems/Fixedpoint.lean`), pasted verbatim. -/

public section

universe u

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence.GammaLow.Glue

/-- **`fixedpoint` (v1, `0 < γ < 1`) from FL-low and LG-low.** -/
theorem fixedpoint_of_low (hFL : WaveTurbulence.GammaLow.Flower.LayergardenFlowerLowGate) (hLG : WaveTurbulence.GammaLow.LGLow.LayergardenLowGate) : WTPrefix fun P =>
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (g : (Fin P.d → ℤ) → Ω → ℂ), IsGaussianData μ g →
    ∀ p : ℕ, p < P.D →
    ∀ (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
      (E : ℕ → (Fin P.d → ℤ) → ℝ)
      (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ),
      (∀ q ≤ p, AnsatzAt P μ g a Fev R E Et q) →
    ∃ F' : Set Ω, F' ⊆ Fev p ∧ MeasurableSet F' ∧ IsSymmetricEvent P.L P.φin g F' ∧
      μ.real (Fev p \ F') ≤ Real.exp (-(4 * P.N (p + 1) : ℝ)) ∧
      ∀ ω ∈ F',
        let Ntr := P.N (p + 1)
        let Λ : ℝ := 5 / 4 * P.Lambda (p + 1)
        let ℒ : ℕ → (Icc (p : ℝ) (p + 1) → (Fin P.d → ℤ) → ℂ) →
            Icc (p : ℝ) (p + 1) → (Fin P.d → ℤ) → ℂ :=
          fun j b t n => Lop P.L P.γ P.δ p Ntr (a ω p) j b t n
        let Zs := ZSpace (d := P.d) P.L Λ p
        (∀ t ∈ Icc (p : ℝ) (p + 1), ∀ n,
          ‖aTr P.L P.γ P.δ p Ntr (a ω p) t n‖ ≤
            jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) *
              Real.exp (3 * Ntr)) ∧
        (∀ (b : Icc (p : ℝ) (p + 1) → (Fin P.d → ℤ) → ℂ) (t : Icc (p : ℝ) (p + 1)) (n),
          ‖ℒ 0 b t n‖ ≤ jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) *
            Real.exp (-(20 * Ntr : ℝ))) ∧
        (∀ b ∈ Zs, b - ℒ 1 b ∈ Zs) ∧
        (∀ c ∈ Zs, ∃! b, b ∈ Zs ∧ b - ℒ 1 b = c) ∧
        (∀ b ∈ Zs, ZNorm P.L Λ b ≤ ENNReal.ofReal (Real.exp (3 * Ntr)) * ZNorm P.L Λ (b - ℒ 1 b)) ∧
        (∀ b ∈ Zs, ZNorm P.L Λ b ≤ ENNReal.ofReal (Real.exp (-(10 * Ntr : ℝ))) →
          ∃ c ∈ Zs, c - ℒ 1 c = ℒ 0 b + ℒ 2 b + ℒ 3 b ∧
            ZNorm P.L Λ c ≤ ENNReal.ofReal (Real.exp (-(10 * Ntr : ℝ)))) ∧
        (∀ b ∈ Zs, ∀ b' ∈ Zs, ∀ c ∈ Zs, ∀ c' ∈ Zs,
          ZNorm P.L Λ b ≤ ENNReal.ofReal (Real.exp (-(10 * Ntr : ℝ))) →
          ZNorm P.L Λ b' ≤ ENNReal.ofReal (Real.exp (-(10 * Ntr : ℝ))) →
          c - ℒ 1 c = ℒ 0 b + ℒ 2 b + ℒ 3 b → c' - ℒ 1 c' = ℒ 0 b' + ℒ 2 b' + ℒ 3 b' →
          ZNorm P.L Λ (c - c') ≤ 2⁻¹ * ZNorm P.L Λ (b - b')) := by
  have hG : WTPrefixP X2E.B112Body := layergardenFlower_v4_of_low hFL
  have hL : WTPrefix Gates.LayergardenBody := layergarden_of_low hLG
  have hW : WTPrefix Gates.WkeTaylorBody := WaveTurbulence.wkeTaylor
  exact toFull (V2Chain.fixedpointS_of_parts (S := Set.univ)
    (V2Chain.cplMomentsS_of_gates (V2Chain.WTPrefixPS.ofFull hG) (V2Chain.WTPrefixS.ofFull hL)
      (V2Chain.WTPrefixS.ofFull hW) Cpl.oX3Cpl)
    (V2Chain.part2S_of_X2 (V2Chain.flowerest1S_of_gates (V2Chain.WTPrefixPS.ofFull hG) X2E.oX2Exp)))

end WaveTurbulence.GammaLow.Glue
