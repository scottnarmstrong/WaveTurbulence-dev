/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourcePairEnvelopes
public import WaveTurbulence.Foundations.SumintPar.StaticMassEnvelopeReduction

/-!
# The actual source static mass satisfies the uniform block reduction

All pair envelopes are constructed from the proved source window
estimates. No envelope premise is imposed on the source expression.
The distinguished linear and normal masses remain literal until the
separate block power estimates are inserted.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set ENNReal

namespace WaveTurbulence.SumintPar

/-- TARGET sumint Step 2: unconditional block reduction of the actual localized source static mass. -/
theorem exists_source_static_block_reduction (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : 0 < η) (hηsmall : η ≤ 1/3)
    (τstar : ℝ) (hτstar : 0 < τstar) (β : ℝ) (hβ : 0 < β)
    (hβγ : β/2 < 2*γ) (hβη : β/2 < 2*((d:ℝ)-1)*(1-γ)-η) :
    ∃ C CsA CmA CsC CmC : ℝ, 1 ≤ C ∧ 0 ≤ CsA ∧ 0 ≤ CmA ∧ 0 ≤ CsC ∧ 0 ≤ CmC ∧
      ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) 1 → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (A : ℝ), D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c : ℝ),
      (∫⁻ τ in Icc (enlargedTimeLower D c (L^(-β))) (enlargedTimeUpper D c (L^(-β))) ∩ staticTimeDomain D,
        ‖cutoffPhaseSum D L γ δ η p ν r t τ‖ₑ) ≤
      ∏ i : Fin D.S.I, linearFactorMass D L γ δ p ν r t c (L^(-β)) i *
        (∏ j : Fin (D.S.m i), sourcePairEnvelope D L γ δ η β τstar C CsA CmA CsC CmC ⟨i,j⟩)*
        normalMassInBlock D.S (normalFactorMass D L γ δ p ν r t
          (enlargedTimeLower D c (L^(-β))) (enlargedTimeUpper D c (L^(-β)))) i := by
  obtain ⟨C,CsA,CmA,CsC,CmC,hC,hCsA,hCmA,hCsC,hCmC,hbound⟩ :=
    exists_source_pair_envelopes d hd γ hγ η hη hηsmall τstar hτstar β hβ hβγ hβη
  refine ⟨C,CsA,CmA,CsC,CmC,hC,hCsA,hCmA,hCsC,hCmC,?_⟩
  intro δ N hδ hτ
  obtain ⟨R,hR,hpair⟩ := hbound δ N hδ hτ
  refine ⟨R,hR,?_⟩
  intro L hL D A hD p ν r t c
  have hLp : 0 < L := by linarith [hR.trans hL]
  exact static_mass_uniform_pair_envelope_reduction D hD hLp δ p ν r t c (L^(-β))
    (sourcePairEnvelope D L γ δ η β τstar C CsA CmA CsC CmC)
    (fun u a => hpair L hL D A hD p ν r t c u a)

end WaveTurbulence.SumintPar
