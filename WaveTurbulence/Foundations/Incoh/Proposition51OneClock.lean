/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.Proposition51

/-!
# TARGET Proposition 5.1 for the finite source carrier

The two actual source norms have one constant and one threshold, independent of source order.
The couple has exactly one source root clock; the other external clock is passive.
Instantiation with frozen gardens belongs to C2, after the Wave B freeze.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- TARGET `proplayer1` / `layerregest1`, for actual finite source couple and tree data.
The couple is the TARGET L1049 one-trivial-tree case.
The factor two is an explicit admissible constant in the printed `≲₁` estimate.
All spectral regularity, localization, root summation and differentiation are proved internally. -/
theorem exists_proposition51_oneClock (d : ℕ) (hd : 3 ≤ d) (η : ℝ) (hη : 0 < η)
    (hη₁ : η ≤ 1 / 100) (hsmall : (100 * (d : ℝ)) ^ 2 * η ≤ 1)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ l : ℕ, l ≤ 2 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n mc wc mt wt : ℕ,
        mc ≤ 3 * n → mt + 1 ≤ 3 * n →
        ∀ Pc : MomentumTreeData n mc wc, ∀ Pt : MomentumTreeData n mt wt,
        RootInputCoordinates Pc →
        (∀ i p, p ∈ (Pc.tree i).leaves → Pc.leafInput i p ≠ none) →
        ∀ Qc Qt : Fin n → LayerLink d,
        (∀ i, |((Qc i).leftLayer : ℝ) - (Qc i).rightLayer| + 1 ≤ D) →
        (∀ i, |((Qt i).leftLayer : ℝ) - (Qt i).rightLayer| + 1 ≤ D) →
        1 ≤ incoherenceCount Qc → incoherenceCount Qt = incoherenceCount Qc →
        ∀ v : Fin n × Fin 2, ∀ a : Fin 2, ∀ b : ℝ,
        ∀ Rt : RootCoordinates n, ∀ T : TreeClockFibers l Qt,
        Rt.rootVertex 0 = T.selection.coordinates.rootVertex 0 →
        Rt.rootVertex 1 = T.selection.coordinates.rootVertex (Fin.last (l + 1)) →
        (∀ v ∈ Rt.rootBox Qt, ∀ j, χ (v j) = 1) →
        (∀ v ∈ T.selection.coordinates.rootBox Qt, ∀ j, χ (v j) = 1) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Qc i)) →
        ∀ fc : Fin mc → Mom d → ℂ, ∀ ft : Fin mt → Mom d → ℂ,
        (∀ a, Fourier.spatialNorm (40 * d) (40 * d) (fc a) ≤ ENNReal.ofReal B) →
        (∀ a, Fourier.spatialNorm (40 * d) (40 * d) (ft a) ≤ ENNReal.ofReal B) →
        ∀ ζc ζt : Circle, ∀ Ac At : Set (Mom d),
        Fourier.mixedRestrictionNorm η (30 * d) (30 * d) (vertexClockBox v a Qc b) Ac
          (fun t k => Pc.sourceVertexClockKernel ζc v a L γ δ Qc I fc t k) +
        Fourier.mixedRestrictionNorm η (30 * d) 0 (Rt.rootBox Qt ∩ {t | t 1 < t 0}) At
          (fun t k => Pt.sourceTreeKernel ζt Rt L γ δ Qt T.timeDomain ft t k) ≤
            2 * ENNReal.ofReal ((C₁ * δ) ^ n *
              L ^ (-(incoherenceExponent d γ - Real.sqrt η) * incoherenceCount Qc)) := by
  obtain ⟨Cc, hCc, hc⟩ := exists_rawVertexClockKernel_propositionRate d hd η hη (by linarith only [hη₁]) hsmall B hB
  obtain ⟨Ct, hCt, ht⟩ := exists_rawTreeKernel_propositionRate d hd B hB
  refine ⟨max Cc Ct, hCc.trans_le (le_max_left _ _), ?_⟩
  intro l hl χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨Lc, hLc, hc⟩ := hc γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨Lt, hLt, ht⟩ := ht l hl η hη hη₁ hsmall χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  refine ⟨max Lc Lt, hLc.trans (le_max_left _ _), ?_⟩
  intro L hL n mc wc mt wt hmc hmt Pc Pt Cr hinputs Qc Qt hspanc hspant hg hcount
    v a b Rt T hfirst hlast hχroot hχsel I hI hbox fc ft hfc hft ζc ζt Ac At
  have hc' := hc L ((le_max_left _ _).trans hL) n mc wc hmc Pc Cr hinputs Qc hspanc hg v a b
    I hI hbox fc hfc ζc Ac
  have ht' := ht L ((le_max_right _ _).trans hL) n mt wt hmt Pt Qt hspant (hcount.symm ▸ hg) Rt T
    hfirst hlast hχroot hχsel ft hft ζt At
  rw [hcount] at ht'
  have hr : 0 ≤ L ^ (-(incoherenceExponent d γ - Real.sqrt η) * incoherenceCount Qc) :=
    Real.rpow_nonneg (zero_le_one.trans (hLc.trans ((le_max_left _ _).trans hL))) _
  have hcmax := hc'.trans (sourceRate_mono_constant hCc.le (le_max_left Cc Ct) hδ.le hr n)
  have htmax := ht'.trans (sourceRate_mono_constant hCt.le (le_max_right Cc Ct) hδ.le hr n)
  simpa only [two_mul] using add_le_add hcmax htmax

end WaveTurbulence.Incoh
