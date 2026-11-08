/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.Final
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

/-- **(A) at `S = none`.** -/
def V5FrontierTopClassBoundNoneAt (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D → ∀ (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ), 0 ≤ B₀ →
    (∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (_hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (kind : Bool),
      CanonicalObject p kind (layeredReconstruction RD hG layer hLayer) → (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℝ)
      (g : Fin w → Mom P.d → ℂ) (cψ : ℝ), 1 ≤ cψ → (∀ j, GPresented (32 * P.d) (g j) cψ) →
      (∀ j x, (g j x).im = 0) →
    RowCoherent hM9 B RD hG layer hLayer (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ h p →
    XNorm00Restr (2 * P.η ^ 8) (Eng.outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (Eng.outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (fun tt E => twistedRecenteredModCX G a
        (canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B))
        (fun z => regionBondWeight (topPsi p (g a.1.1)) P.L wBar z) P.L P.γ P.δ h wBar lam
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) ≤
    ENNReal.ofReal (cψ ^ (3 * U.card)) * ENNReal.ofReal ((1 + |lam|) ^ (6 * P.η ^ 6) * ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 / 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀)))

/-- Gate form (every constant before the record `P`). -/
def V5FrontierTopClassBoundNone : Prop := WTPrefix V5FrontierTopClassBoundNoneAt

/-- `topPsi p g` is top-supported (the R135 orientation: far layer `< p`, near layer `= p`). -/
theorem topPsi_topSupported {w d : ℕ} (p : ℕ) (g : Fin w → Mom d → ℂ) :
    TopSupported p (fun j => topPsi p (g j)) := by
  intro j q q' h
  funext k
  simp [topPsi, h]

/-- The constant `1` has a presentation of mass `1`. -/
theorem one_presented {d : ℕ} :
    ∃ (α : Type) (_ : MeasurableSpace α) (M : Cut2A.SpatialMeasure (Mom d) α),
      M.mass ≤ 1 ∧ ∀ x, M.value x = 1 := by
  refine ⟨Unit, inferInstance,
    { μ := Measure.dirac ()
      sigmaFinite := inferInstance
      frequency := fun _ => 0
      frequency_measurable := measurable_const
      amplitude := fun _ => 1
      amplitude_integrable := integrable_const _ }, ?_, ?_⟩
  · simp [Cut2A.SpatialMeasure.mass]
  · intro x
    simp [Cut2A.SpatialMeasure.value]

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

/-- `topPsi p (g ·)` is spatially presented with mass `cψ`, from `GPresented`. -/
theorem topPsi_spatialPresented {w d : ℕ} (p : ℕ) (g : Fin w → Mom d → ℂ) {J : ℕ} {c : ℝ}
    (hc : 1 ≤ c) (hg : ∀ j, GPresented J (g j) c) :
    SpatialPresented (fun j => topPsi p (g j)) c := by
  intro j q q'
  by_cases h : q < p ∧ q' = p
  · simpa [topPsi, h] using presented_of_gPresented (by linarith) (hg j)
  · obtain ⟨α, i, M, hM, hv⟩ := one_presented (d := d)
    exact ⟨α, i, M, hM.trans hc, by simp [topPsi, h, hv]⟩

theorem wtPrefix_mono {Q Q' : WTParams → Prop} (h : WTPrefix Q) (hQ : ∀ P, Q P → Q' P) : WTPrefix Q' := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ hδ D hD hτD
  exact ⟨C₂, hC₂, L₀, hL₀, fun L hL => hQ _ (H L hL)⟩

/-- **A2 (pointwise).** `V5BondClassBoundAt P` gives case (A) at `S = none` at the same record. -/
theorem v5FrontierTopClassBoundNoneAt_of_bondAt (P : WTParams) (H : V5BondClassBoundAt P) :
    V5FrontierTopClassBoundNoneAt P := by
  intro p hp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam
    g cψ hc hg _hreal hcoh
  exact H hp h B₀ hB₀ hh hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam
    (fun j => topPsi p (g j)) cψ hc (topPsi_topSupported p g) (topPsi_spatialPresented p g hc hg) hcoh

/-- **A2.** `V5BondClassBound` gives case (A) at `S = none`. -/
theorem v5FrontierTopClassBoundNone_of_bond (H : V5BondClassBound) : V5FrontierTopClassBoundNone :=
  wtPrefix_mono H v5FrontierTopClassBoundNoneAt_of_bondAt

/-- **A2 export.** Case (A) at `S = none`, from the W2 certificate and the leafwise/reality gates
(the inputs of `v5BondClassBound_of_uniformCert`). -/
theorem v5FrontierTopClassBoundNone_of_uniformCert :
    UniformTermCertTargetK → LeafwiseCoherentApproximationGate → LeafwiseIncoherentDecayGate → RealityAll →
      V5FrontierTopClassBoundNone :=
  fun hU hG hI hR => v5FrontierTopClassBoundNone_of_bond (v5BondClassBound_of_uniformCert hU hG hI hR)

end WaveTurbulence.Flower.V5WA
