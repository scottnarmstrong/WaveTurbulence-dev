/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.Weight
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.WeightedMerge
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.Pullback
public import WaveTurbulence.Foundations.VineEst.VineSpaceK.Statements
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.UniformIface
public import WaveTurbulence.Foundations.Flower.Stage1W.Defs

/-! # V5W-A2: case (A) of the weighted vine estimate at `S = none`

`V5FrontierTopClassBoundNoneAt` is the S-V5W statement `V5FrontierTopClassBoundAt` (SCOPE §2.1) at `S = none`:
main's `V5BondClassBoundAt` with the label weight `ψ = topPsi p (g ·)` in place of an abstract top-supported spatially
presented `ψ` (binders `g`, `cψ`, `GPresented (32 d)`, real values). At `S = none` the stem filter is absent
(`topFilterWeight none ≡ 1`), so neither `nodeWeight` nor `topFilterMass` occurs. Proved from `V5BondClassBound`
(ported V5-SPACE-EXT, `v5BondClassBound_of_uniformCert`). -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
noncomputable section
namespace WaveTurbulence.Flower.V5WA
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13
  WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineSpaceK WaveTurbulence.VineSpaceB
  WaveTurbulence.Flower.Stage1W
open VineEstS5C.P4.Final LGSpine
open scoped ENNReal

/-- A `GPresented` weight has a presentation of mass at most `c` (`0 ≤ c`). -/
theorem presented_of_gPresented {d J : ℕ} {g : Mom d → ℂ} {c : ℝ} (hc : 0 ≤ c) (h : GPresented J g c) :
    ∃ (α : Type) (_ : MeasurableSpace α) (M : Cut2A.SpatialMeasure (Mom d) α),
      M.mass ≤ c ∧ ∀ x, M.value x = g x := by
  obtain ⟨α, _, M, hM, hv⟩ := h
  refine ⟨α, inferInstance, M, ?_, hv⟩
  have h1 : ∫⁻ a, ‖M.amplitude a‖ₑ ∂M.μ ≤ ENNReal.ofReal c := by
    refine le_trans (lintegral_mono fun a => ?_) hM
    calc ‖M.amplitude a‖ₑ = 1 * ‖M.amplitude a‖ₑ := (one_mul _).symm
      _ ≤ _ := by
        gcongr
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by linarith [norm_nonneg (M.frequency a)]))
  unfold Cut2A.SpatialMeasure.mass
  rw [integral_norm_eq_lintegral_enorm M.amplitude_integrable.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hc h1

end WaveTurbulence.Flower.V5WA
