/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceNormalEnvelopeBlock
public import WaveTurbulence.Foundations.Sumint.SourceBadLinearEnvelopeBlock
public import WaveTurbulence.Foundations.Sumint.SourceBadFirstEnvelopeBlock
public import WaveTurbulence.Foundations.Sumint.SourceCaseBProducts

/-!
# Every actual source envelope block satisfies the common power budget

The admissible datum supplies positivity of the first-pair length in
cases (a) and (c). The literal finite bad-kind flag exhausts the four
source cases. One common constant is chosen before delta and Dsteps.
-/

public section

open MeasureTheory Set ENNReal
open scoped Classical

namespace WaveTurbulence.Sumint

/-- TARGET sumint Step 2: all actual source envelope blocks obey one uniform arity/count budget. -/
theorem exists_source_all_envelope_block_bounds (d : ℕ) (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Ioo (0:ℝ) 1) (hη : η ≤ gammaBase γ) (hηsmall : η ≤ 1/24)
    (τstar : ℝ) (hτstar : 0 < τstar) (β : ℝ) (hβ : 0 < β) (hβγ : β < 20*γ)
    (hhigh : 1/2 < γ → β/20 < min (2*γ-1) (1-γ))
    (C CsA CmA CsC CmC : ℝ) (hCsA : 0 ≤ CsA) (hCmA : 0 ≤ CmA)
    (hCsC : 0 ≤ CsC) (hCmC : 0 ≤ CmC) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ δ : ℝ, δ ∈ Ioc (0:ℝ) (1/16) →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (N : ℕ), τstar = (N:ℝ)*δ →
      ∀ A : ℝ, D.Admissible A L γ η N → γ+η ≤ 1 →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d),
      1/L ≤ ‖r‖ → ‖r‖ ≤ L^(-γ+η) →
      ∀ (t c : ℝ) (i : Fin D.S.I),
      ((caseBMultiplier D r i*linearFactorMass D L γ δ p ν r t c (L^(-β)) i)*
        (∏ j : Fin (D.S.m i), sourcePairEnvelope D L γ δ η β τstar C CsA CmA CsC CmC ⟨i,j⟩)*
        normalMassInBlock D.S (normalFactorMass D L γ δ p ν r t
          (enlargedTimeLower D c (L^(-β))) (enlargedTimeUpper D c (L^(-β)))) i) ≤
      ENNReal.ofReal (G^(D.S.n i)*δ^(-(D.S.n i:ℝ)/2)*
        L^((D.S.n i:ℝ)*((d:ℝ)-γ)+badBlockCost D γ i-(β/20)*(blockDiscrepancy D i:ℝ))) := by
  obtain ⟨Cn,hCn,hNormal⟩ := exists_source_normal_envelope_block_bound d hd γ hγ τstar hτstar β hβ hβγ hhigh
  let G := max 1 (max C Cn)
  have hG : 1 ≤ G := le_max_left _ _
  have hCG : C ≤ G := (le_max_left _ _).trans (le_max_right _ _)
  have hCnG : Cn ≤ G := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨G,hG,?_⟩
  intro δ hδ
  obtain ⟨RN,hRN,hN⟩ := hNormal G hG hCnG δ hδ
  obtain ⟨RB,hRB,hB⟩ := exists_source_bad_linear_envelope_block_bound d hγ β hβ.le δ hδ
  obtain ⟨RF,hRF,hF⟩ := exists_source_bad_first_envelope_block_bound d hd hγ hη hηsmall
    τstar hτstar β hβ.le C CsA CmA CsC CmC δ hCsA hCmA hCsC hCmC hδ
  refine ⟨max RN (max RB RF),hRN.trans (le_max_left _ _),?_⟩
  intro L hL D N hτ A hD hγη p ν r hr hrupper t c i
  have hLRN : RN ≤ L := (le_max_left _ _).trans hL
  have hLRB : RB ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLRF : RF ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  by_cases hn : D.S.nor i = true
  · have hmult : caseBMultiplier D r i = 1 := by simp [caseBMultiplier,hn]
    have hcost : badBlockCost D γ i = 0 := by simp [badBlockCost,hn]
    have hb := hN L hLRN D N hτ A η hD hγη p ν r hr hrupper t c C CsA CmA CsC CmC ⟨i,hn⟩ hCG
    simpa only [hmult,one_mul,hcost,add_zero] using hb
  · have hn' : D.S.nor i = false := Bool.eq_false_iff.mpr hn
    by_cases hk : D.badKind i = 0 ∨ D.badKind i = 2
    · have hm : 0 < D.S.m i := by
        rcases hk with h0 | h2
        · exact ((hD.2.2.2.2.2.2.2.2.2 i hn').1 h0).choose
        · exact (hD.2.2.2.2.2.2.2.2.2 i hn').2.1 h2
      have hnot1 : D.badKind i ≠ 1 := by rcases hk with h0 | h2 <;> omega
      have hmult : caseBMultiplier D r i = 1 := by simp [caseBMultiplier,hn',hnot1]
      simpa only [hmult,one_mul] using hF L hLRF D hγη p ν r hr hrupper t c G i hG hCG hn' hk hm
    · have hk' : D.badKind i = 1 ∨ D.badKind i = 3 := by omega
      have hmult : caseBMultiplier D r i = (if D.badKind i = 1 then ENNReal.ofReal ‖r‖ else 1) := by
        simp only [caseBMultiplier,hn',true_and]
      simpa only [hmult] using hB L hLRB D η hγη p ν r hr hrupper t c τstar C G CsA CmA CsC CmC i hG hCG hn' hk'

end WaveTurbulence.Sumint
