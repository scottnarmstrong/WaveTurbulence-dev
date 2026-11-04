/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceSpecialCoreMass
public import WaveTurbulence.Foundations.Sumint.SourceFirstPairCombinedEnvelope

/-!
# Actual first bad coarse cores retain their bad and discrepancy gains

Both the pair envelope and the distinguished linear estimate are proved
source bounds. The original middle-time strip is retained in the actual
core reduction before inserting these uniform estimates.
-/

public section
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.Sumint

/-- TARGET sumint Step 3: the actual untouched first bad core keeps its three-input bad and discrepancy gains. -/
theorem exists_source_special_core_power_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : 0 < η) (hηbase : η ≤ gammaBase γ)
    (hηsmall : η ≤ 1/24) (hγη : γ+η ≤ 1)
    (τstar : ℝ) (hτstar : 0 < τstar) (β : ℝ) (hβ : 0 < β)
    (hβγ : β/2 < 2*γ) (hβη : β/2 < 2*((d:ℝ)-1)*(1-γ)-η)
    (δ : ℝ) (N : ℕ) (hδ : δ ∈ Ioc (0:ℝ) (1/16)) (hτ : τstar = (N:ℝ)*δ) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (A : ℝ), D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d),
      1/L ≤ ‖r‖ → ‖r‖ ≤ L^(-γ+η) → ∀ (t c : ℝ)
      (a : Σ i : Fin D.S.I, Fin (D.S.m i)), caseAPair D a ∨ caseCPair D a →
      (∫⁻ z, sourceCoreNormFactor D L γ δ η p ν r t c (L^(-β)) (.inl a.1) z) ≤
        ENNReal.ofReal (L^(3*((d:ℝ)-γ)-gammaBase γ/4-(if pairIncoherent D a then β/20 else 0))) := by
  obtain ⟨C,CsA,CmA,CsC,CmC,hC,hCsA,hCmA,hCsC,hCmC,hpair⟩ :=
    exists_source_pair_envelopes d hd γ hγ η hη (by linarith only [hηsmall]) τstar hτstar β hβ hβγ hβη
  obtain ⟨RP,hRP,hP⟩ := hpair δ N ⟨hδ.1,by linarith only [hδ.2]⟩ hτ
  obtain ⟨RF,hRF,hF⟩ := exists_source_first_pair_combined_envelope_bound d hd hγ hηbase hηsmall
    τstar hτstar β hβ.le C CsA CmA CsC CmC δ hCsA hCmA hCsC hCmC hδ
  refine ⟨max RP RF,hRP.trans (le_max_left _ _),?_⟩
  intro L hL D A hD p ν r hr hrupper t c a ha
  have hLP : RP ≤ L := (le_max_left _ _).trans hL
  have hLF : RF ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := by linarith only [hRP,hLP]
  exact (lintegral_sourceCore_special_le_uniform_pair_bound D hLp γ δ η p ν r t c (L^(-β)) a ha
    (sourcePairEnvelope D L γ δ η β τstar C CsA CmA CsC CmC a)
    (fun u => hP L hLP D A hD p ν r t c u a)).trans
      (hF L hLF D hγη p ν r hr hrupper t c a ha)

end WaveTurbulence.Sumint
