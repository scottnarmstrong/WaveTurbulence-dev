/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceBadLinearBounds
public import WaveTurbulence.Foundations.Sumint.SourceOrdinaryPairBudget
public import WaveTurbulence.Foundations.Sumint.PairArityBudget
public import WaveTurbulence.Foundations.Sumint.SourceBlockExponents

/-!
# Actual case-(b)/(d) blocks in the common source envelope budget

The distinguished core has one input. Every pair is ordinary. Case (b)
includes its literal external momentum norm, while case (d) retains the
linear cost paid by the source weight multiplicity. Their arities and
local discrepancy counts are kept exact.
-/

public section

open MeasureTheory Set ENNReal
open scoped Classical

namespace WaveTurbulence.Sumint

/-- Actual case-(b)/(d) envelope blocks fit the common input-arity and discrepancy budget. -/
theorem exists_source_bad_linear_envelope_block_bound (d : ℕ) {γ : ℝ}
    (hγ : γ ∈ Ioo (0:ℝ) 1) (β : ℝ) (hβ : 0 ≤ β)
    (δ : ℝ) (hδ : δ ∈ Ioc (0:ℝ) (1/16)) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (η : ℝ), γ+η ≤ 1 →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d),
      1/L ≤ ‖r‖ → ‖r‖ ≤ L^(-γ+η) →
      ∀ (t c τstar C G CsA CmA CsC CmC : ℝ) (i : Fin D.S.I), 1 ≤ G → C ≤ G →
      D.S.nor i = false → (D.badKind i = 1 ∨ D.badKind i = 3) →
      ((if D.badKind i = 1 then ENNReal.ofReal ‖r‖ else 1)*linearFactorMass D L γ δ p ν r t c (L^(-β)) i)*
        (∏ j : Fin (D.S.m i), sourcePairEnvelope D L γ δ η β τstar C CsA CmA CsC CmC ⟨i,j⟩)*
        normalMassInBlock D.S (normalFactorMass D L γ δ p ν r t
          (enlargedTimeLower D c (L^(-β))) (enlargedTimeUpper D c (L^(-β)))) i ≤
      ENNReal.ofReal (G^(D.S.n i)*δ^(-(D.S.n i:ℝ)/2)*
        L^((D.S.n i:ℝ)*((d:ℝ)-γ)+badBlockCost D γ i-(β/20)*(blockDiscrepancy D i:ℝ))) := by
  obtain ⟨RB,hRB,hB⟩ := exists_source_case_b_linear_bound d hγ δ hδ.1 hδ.2
  obtain ⟨RD,hRD,hDlinear⟩ := exists_source_case_d_linear_bound d hγ δ hδ.1 hδ.2
  refine ⟨max RB RD,hRB.trans (le_max_left _ _),?_⟩
  intro L hL D η hγη p ν r hr hrupper t c τstar C G CsA CmA CsC CmC i hG hCG hn hk
  have hLRB : RB ≤ L := (le_max_left _ _).trans hL
  have hLRD : RD ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := by linarith [hRB.trans hLRB]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hδ1 : δ ∈ Ioc (0:ℝ) 1 := ⟨hδ.1,by linarith [hδ.2]⟩
  have hh : L^(-β) ∈ Icc (0:ℝ) 1 := ⟨Real.rpow_nonneg hLp.le _,
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (neg_nonpos.mpr hβ)⟩
  let χ (j : Fin (D.S.m i)) : ℕ := if pairIncoherent D ⟨i,j⟩ then 1 else 0
  let F := (if D.badKind i = 1 then ENNReal.ofReal ‖r‖ else 1)*linearFactorMass D L γ δ p ν r t c (L^(-β)) i
  have hP (j : Fin (D.S.m i)) : sourcePairEnvelope D L γ δ η β τstar C CsA CmA CsC CmC ⟨i,j⟩ ≤
      ENNReal.ofReal (G^2*δ⁻¹*L^(2*((d:ℝ)-γ)-(β/20)*(χ j:ℝ))) := by
    have hna : ¬ caseAPair D ⟨i,j⟩ := by
      rintro ⟨_,h0,_⟩
      change D.badKind i = 0 at h0
      rcases hk with h1 | h3 <;> omega
    have hnc : ¬ caseCPair D ⟨i,j⟩ := by
      rintro ⟨_,h2,_⟩
      change D.badKind i = 2 at h2
      rcases hk with h1 | h3 <;> omega
    have hb := sourcePairEnvelope_le_ordinary_budget D hL1 hδ.1 hβ hG hCG
      γ η τstar CsA CmA CsC CmC ⟨i,j⟩ hna hnc
    by_cases hq : pairIncoherent D ⟨i,j⟩ <;> simpa [χ,hq] using hb
  have hcore : F ≤ ENNReal.ofReal (L^(((d:ℝ)-γ)+badBlockCost D γ i)) := by
    rcases hk with hb | hd
    · have hnot3 : D.badKind i ≠ 3 := by rw [hb]; decide
      have hrp : 0 < ‖r‖ := (one_div_pos.mpr hLp).trans_le hr
      have hbound := hB L hLRB D η hγη p ν r (norm_pos_iff.mp hrp) hrupper t c (L^(-β)) i hh
      dsimp only [F]
      rw [ite_eq_left hb,badBlockCost,ite_eq_left hn,ite_eq_right hnot3]
      apply hbound.trans
      apply ENNReal.ofReal_le_ofReal
      apply Real.rpow_le_rpow_of_exponent_le hL1
      linarith only [gammaBase_pos hγ]
    · have hnot1 : D.badKind i ≠ 1 := by rw [hd]; decide
      dsimp only [F]
      rw [ite_eq_right hnot1,one_mul,badBlockCost,ite_eq_left hn,ite_eq_left hd]
      exact hDlinear L hLRD D η hγη p ν r hr hrupper t c (L^(-β)) i hh
  have hcore' : F ≤ ENNReal.ofReal (G^1*δ^(-((1:ℕ):ℝ)/2)*L^(((d:ℝ)-γ)+badBlockCost D γ i)) :=
    hcore.trans (ENNReal.ofReal_le_ofReal (by
      simpa only [Nat.cast_one] using
        (lattice_power_le_local_budget (e := ((d:ℝ)-γ)+badBlockCost D γ i) 1 hG hδ1 hLp)))
  have hb := core_mul_pair_arity_budget
    (fun j : Fin (D.S.m i) => sourcePairEnvelope D L γ δ η β τstar C CsA CmA CsC CmC ⟨i,j⟩)
    χ 1 (zero_le_one.trans hG) hδ.1 hLp hcore' hP
  have hn' : 1+2*D.S.m i = D.S.n i := by simp [SumintShape.n,hn]; omega
  have hnotNor : ¬ D.S.nor i = true := by rw [hn]; decide
  have hc : (∑ j, χ j) = blockDiscrepancy D i := by
    rw [blockDiscrepancy,dite_eq_right hnotNor,add_zero]
  have hexp : (((d:ℝ)-γ)+badBlockCost D γ i)+
      (((2*D.S.m i:ℕ):ℝ)*((d:ℝ)-γ)-(β/20)*((∑ j, χ j):ℝ)) =
      (D.S.n i:ℝ)*((d:ℝ)-γ)+badBlockCost D γ i-(β/20)*(blockDiscrepancy D i:ℝ) := by
    rw [← hn',← hc]
    push_cast
    ring
  rw [Fintype.card_fin,hn',hexp] at hb
  rw [normalMassInBlock,dite_eq_right hnotNor,mul_one]
  exact hb

end WaveTurbulence.Sumint
