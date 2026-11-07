/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceFirstPairCombinedEnvelope
public import WaveTurbulence.Foundations.SumintPar.SourceOrdinaryPairBudget
public import WaveTurbulence.Foundations.SumintPar.FirstPairRemainder
public import WaveTurbulence.Foundations.SumintPar.PairArityBudget
public import WaveTurbulence.Foundations.SumintPar.SourceBlockExponents

/-!
# Actual case-(a)/(c) blocks in the common source envelope budget

The distinguished first pair and linear mass form a three-input core.
Every remaining pair uses the ordinary two-input bound. The remainder
keeps its original source indices, and its discrepancy sum together
with the first pair is precisely the literal local source count.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set ENNReal
open scoped Classical

namespace WaveTurbulence.SumintPar

/-- Actual case-(a)/(c) source envelope blocks satisfy their full arity and discrepancy budget. -/
theorem exists_source_bad_first_envelope_block_bound (d : ℕ) (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Ioo (0:ℝ) 1) (hη : η ≤ gammaBase γ) (hηsmall : η ≤ 1/24)
    (τstar : ℝ) (hτstar : 0 < τstar) (β : ℝ) (hβ : 0 ≤ β)
    (C CsA CmA CsC CmC δ : ℝ) (hCsA : 0 ≤ CsA) (hCmA : 0 ≤ CmA)
    (hCsC : 0 ≤ CsC) (hCmC : 0 ≤ CmC) (hδ : δ ∈ Ioc (0:ℝ) (1/16)) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d), γ+η ≤ 1 →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d),
      1/L ≤ ‖r‖ → ‖r‖ ≤ L^(-γ+η) →
      ∀ (t c G : ℝ) (i : Fin D.S.I), 1 ≤ G → C ≤ G →
      D.S.nor i = false → (D.badKind i = 0 ∨ D.badKind i = 2) → 0 < D.S.m i →
      linearFactorMass D L γ δ p ν r t c (L^(-β)) i *
        (∏ j : Fin (D.S.m i), sourcePairEnvelope D L γ δ η β τstar C CsA CmA CsC CmC ⟨i,j⟩)*
        normalMassInBlock D.S (normalFactorMass D L γ δ p ν r t
          (enlargedTimeLower D c (L^(-β))) (enlargedTimeUpper D c (L^(-β)))) i ≤
      ENNReal.ofReal (G^(D.S.n i)*δ^(-(D.S.n i:ℝ)/2)*
        L^((D.S.n i:ℝ)*((d:ℝ)-γ)+badBlockCost D γ i-(β/20)*(blockDiscrepancy D i:ℝ))) := by
  obtain ⟨R,hR,hfirst⟩ := exists_source_first_pair_combined_envelope_bound d hd hγ hη hηsmall
    τstar hτstar β hβ C CsA CmA CsC CmC δ hCsA hCmA hCsC hCmC hδ
  refine ⟨R,hR,?_⟩
  intro L hL D hγη p ν r hr hrupper t c G i hG hCG hn hk hm
  have hL1 : 1 ≤ L := by linarith [hR.trans hL]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hδ1 : δ ∈ Ioc (0:ℝ) 1 := ⟨hδ.1,by linarith [hδ.2]⟩
  let j₀ : Fin (D.S.m i) := ⟨0,hm⟩
  let a₀ : Σ i : Fin D.S.I, Fin (D.S.m i) := ⟨i,j₀⟩
  let P (j : Fin (D.S.m i)) := sourcePairEnvelope D L γ δ η β τstar C CsA CmA CsC CmC ⟨i,j⟩
  let χ (j : Fin (D.S.m i)) : ℕ := if pairIncoherent D ⟨i,j⟩ then 1 else 0
  let F := linearFactorMass D L γ δ p ν r t c (L^(-β)) i * P j₀
  have hnotNor : ¬ D.S.nor i = true := by rw [hn]; decide
  have hnot3 : D.badKind i ≠ 3 := by rcases hk with h0 | h2 <;> omega
  have hcost : badBlockCost D γ i = -gammaBase γ/4 := by
    rw [badBlockCost,ite_eq_left hn,ite_eq_right hnot3]
  have ha₀ : caseAPair D a₀ ∨ caseCPair D a₀ := by
    rcases hk with h0 | h2
    · exact Or.inl ⟨hn,h0,rfl⟩
    · exact Or.inr ⟨hn,h2,rfl⟩
  have hcore : F ≤ ENNReal.ofReal (L^(3*((d:ℝ)-γ)+badBlockCost D γ i-(β/20)*(χ j₀:ℝ))) := by
    have hb := hfirst L hL D hγη p ν r hr hrupper t c a₀ ha₀
    have he : 3*((d:ℝ)-γ)+badBlockCost D γ i-(β/20)*(χ j₀:ℝ) =
        3*((d:ℝ)-γ)-gammaBase γ/4-(if pairIncoherent D a₀ then β/20 else 0) := by
      rw [hcost]
      by_cases hq : pairIncoherent D a₀ <;> simp [χ,a₀,hq] <;> ring
    rw [he]
    exact hb
  have hcore' : F ≤ ENNReal.ofReal (G^3*δ^(-((3:ℕ):ℝ)/2)*
      L^(3*((d:ℝ)-γ)+badBlockCost D γ i-(β/20)*(χ j₀:ℝ))) :=
    hcore.trans (ENNReal.ofReal_le_ofReal (lattice_power_le_local_budget 3 hG hδ1 hLp))
  have hP (j : {j : Fin (D.S.m i) // j ≠ j₀}) : P j ≤
      ENNReal.ofReal (G^2*δ⁻¹*L^(2*((d:ℝ)-γ)-(β/20)*(χ j:ℝ))) := by
    have hj : (j.1:ℕ) ≠ 0 := by
      intro he
      apply j.2
      exact Fin.ext he
    have hns := not_special_pair_of_ne_zero D ⟨i,j.1⟩ hj
    have hb := sourcePairEnvelope_le_ordinary_budget D hL1 hδ.1 hβ hG hCG
      γ η τstar CsA CmA CsC CmC ⟨i,j.1⟩ hns.1 hns.2
    by_cases hq : pairIncoherent D ⟨i,j.1⟩ <;> simpa [P,χ,hq] using hb
  have hb := core_mul_pair_arity_budget (fun j : {j : Fin (D.S.m i) // j ≠ j₀} => P j)
    (fun j => χ j) 3 (zero_le_one.trans hG) hδ.1 hLp hcore' hP
  have hcard : Fintype.card {j : Fin (D.S.m i) // j ≠ j₀} = D.S.m i-1 := by
    simpa only [Fintype.card_fin] using card_first_rest j₀
  have harity : 3+2*Fintype.card {j : Fin (D.S.m i) // j ≠ j₀} = D.S.n i := by
    rw [hcard]
    simp only [SumintShape.n,hn,Bool.false_eq_true,ite_false]
    omega
  have hχ : χ j₀+(∑ j : {j : Fin (D.S.m i) // j ≠ j₀}, χ j) = blockDiscrepancy D i := by
    rw [blockDiscrepancy,dite_eq_right hnotNor,add_zero]
    exact (sum_first_rest j₀ χ).symm
  have hexp : (3*((d:ℝ)-γ)+badBlockCost D γ i-(β/20)*(χ j₀:ℝ))+
      (((2*Fintype.card {j : Fin (D.S.m i) // j ≠ j₀}:ℕ):ℝ)*((d:ℝ)-γ)-
        (β/20)*((∑ j : {j : Fin (D.S.m i) // j ≠ j₀}, χ j):ℝ)) =
      (D.S.n i:ℝ)*((d:ℝ)-γ)+badBlockCost D γ i-(β/20)*(blockDiscrepancy D i:ℝ) := by
    rw [← harity,← hχ]
    push_cast
    ring
  rw [harity,hexp] at hb
  apply le_trans (le_of_eq ?_) hb
  rw [normalMassInBlock,dite_eq_right hnotNor,mul_one,prod_first_rest j₀]
  dsimp only [F,P]
  ac_rfl

end WaveTurbulence.SumintPar
