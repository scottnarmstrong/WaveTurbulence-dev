/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceSpecialCoreIntegrand
public import WaveTurbulence.Foundations.Sumint.TripleLinearPairIntegral
public import WaveTurbulence.Foundations.Sumint.SourceLinearMass

/-!
# The actual first bad core integrates its ordered pair before its linear time

This preserves the source middle-time strip and its uniform pair gain.
The primary reduction uses the actual pair mass without any envelope
hypothesis. A distinctly named conditional corollary accepts a uniform
bound for that mass for subsequent insertion of the proved envelope.
-/

public section
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.Sumint

/-- The actual first bad core mass retains the original ordered pair mass inside its linear integral. -/
theorem lintegral_sourceCore_special_le_pair_mass {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a) :
    (∫⁻ z, sourceCoreNormFactor D L γ δ η p ν r t c h (.inl a.1) z) ≤
      ∫⁻ s in Icc (enlargedTimeLower D c h (.inl ⟨a.1,0⟩)) (enlargedTimeUpper D c h (.inl ⟨a.1,0⟩)),
        ENNReal.ofReal ‖linearTimeSum D L γ δ p ν r t a.1 s‖ *
          orderedPairMass D L γ δ η p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) (fun _ => s) a := by
  let F (s : ℝ) := ENNReal.ofReal ‖linearTimeSum D L γ δ p ν r t a.1 s‖
  let G (s : ℝ) (w : ℝ × ℝ) := ENNReal.ofReal (orderedPairNorm D L γ δ η p ν r t (fun _ => s) a w)
  have hF : Measurable F := (measurable_linearTimeSum_norm D hL γ δ p ν r t a.1).ennreal_ofReal
  have hmap : Measurable (fun x : ℝ × (ℝ × ℝ) => ((fun _ : Fin D.S.I => x.1),x.2)) := by fun_prop
  have hG : Measurable (Function.uncurry G) :=
    ((measurable_orderedPairNorm D hL γ δ η p ν r t a).comp hmap).ennreal_ofReal
  have he := (MeasurePreserving.symm (sourceSpecialCoreGrouping D a ha)
    (volume_preserving_sourceSpecialCoreGrouping D a ha)).lintegral_comp_emb
      (sourceSpecialCoreGrouping D a ha).symm.measurableEmbedding
      (sourceCoreNormFactor D L γ δ η p ν r t c h (.inl a.1))
  rw [← he]
  calc
    _ ≤ ∫⁻ z, (Icc (fun j => enlargedTimeLower D c h (sourceSpecialTime D a j))
        (fun j => enlargedTimeUpper D c h (sourceSpecialTime D a j))).indicator
          (fun z => F (z 2)*G (z 2) (z 0,z 1)) z :=
      lintegral_mono (sourceCoreNormFactor_special_le D L γ δ η p ν r t c h a ha)
    _ = _ := by
      rw [lintegral_indicator measurableSet_Icc]
      have ht := lintegral_triple_linear_pair
        (fun j => enlargedTimeLower D c h (sourceSpecialTime D a j))
        (fun j => enlargedTimeUpper D c h (sourceSpecialTime D a j)) F G hF
        (fun _ => ENNReal.ofReal_ne_top) hG
      have ht0 : sourceSpecialTime D a 0 = .inl ⟨a.1,a.2.succ⟩ := rfl
      have ht1 : sourceSpecialTime D a 1 = .inr (.inl a) := rfl
      have ht2 : sourceSpecialTime D a 2 = .inl ⟨a.1,0⟩ := rfl
      simpa only [F,G,ht0,ht1,ht2,orderedPairMass] using ht

/-- A uniform bound on the literal ordered pair mass may be inserted before the distinguished linear integration. -/
theorem lintegral_sourceCore_special_le_uniform_pair_bound {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a)
    (B : ℝ≥0∞) (hB : ∀ u : Fin D.S.I → ℝ,
      orderedPairMass D L γ δ η p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) u a ≤ B) :
    (∫⁻ z, sourceCoreNormFactor D L γ δ η p ν r t c h (.inl a.1) z) ≤
      linearFactorMass D L γ δ p ν r t c h a.1*B := by
  apply (lintegral_sourceCore_special_le_pair_mass D hL γ δ η p ν r t c h a ha).trans
  calc
    _ ≤ ∫⁻ s in Icc (enlargedTimeLower D c h (.inl ⟨a.1,0⟩)) (enlargedTimeUpper D c h (.inl ⟨a.1,0⟩)),
        ENNReal.ofReal ‖linearTimeSum D L γ δ p ν r t a.1 s‖*B :=
      lintegral_mono (fun s => mul_le_mul' le_rfl (hB (fun _ => s)))
    _ = _ := lintegral_mul_const B
      (measurable_linearTimeSum_norm D hL γ δ p ν r t a.1).ennreal_ofReal

end WaveTurbulence.Sumint
