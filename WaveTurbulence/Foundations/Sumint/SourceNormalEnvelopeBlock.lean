/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceNormalBlockBound
public import WaveTurbulence.Foundations.Sumint.SourceOrdinaryPairBudget
public import WaveTurbulence.Foundations.Sumint.PairArityBudget
public import WaveTurbulence.Foundations.Sumint.SourceBlockExponents

/-!
# Every actual normal block fits the common source envelope budget

The literal linear/normal core uses four inputs. The remaining ordinary
pairs contribute two inputs each. Their discrepancy indicators add to
the exact local count. The common constant is fixed before delta.
-/

public section

open MeasureTheory Set ENNReal
open scoped Classical

namespace WaveTurbulence.Sumint

/-- Actual normal blocks in the source envelope product satisfy their exact arity/discrepancy budget. -/
theorem exists_source_normal_envelope_block_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (τstar : ℝ) (hτstar : 0 < τstar)
    (β : ℝ) (hβ : 0 < β) (hβγ : β < 20*γ)
    (hhigh : 1/2 < γ → β/20 < min (2*γ-1) (1-γ)) :
    ∃ Cn : ℝ, 1 ≤ Cn ∧ ∀ G : ℝ, 1 ≤ G → Cn ≤ G →
      ∀ δ : ℝ, δ ∈ Ioc (0:ℝ) (1/16) → ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (N : ℕ), τstar = (N:ℝ)*δ →
      ∀ A η : ℝ, D.Admissible A L γ η N → γ+η ≤ 1 →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d),
      1/L ≤ ‖r‖ → ‖r‖ ≤ L^(-γ+η) →
      ∀ (t c C CsA CmA CsC CmC : ℝ) (i : {i : Fin D.S.I // D.S.nor i = true}), C ≤ G →
      linearFactorMass D L γ δ p ν r t c (L^(-β)) i.1 *
        (∏ j : Fin (D.S.m i.1), sourcePairEnvelope D L γ δ η β τstar C CsA CmA CsC CmC ⟨i.1,j⟩)*
        normalMassInBlock D.S (normalFactorMass D L γ δ p ν r t
          (enlargedTimeLower D c (L^(-β))) (enlargedTimeUpper D c (L^(-β)))) i.1 ≤
      ENNReal.ofReal (G^(D.S.n i.1)*δ^(-(D.S.n i.1:ℝ)/2)*
        L^((D.S.n i.1:ℝ)*((d:ℝ)-γ)-(β/20)*(blockDiscrepancy D i.1:ℝ))) := by
  obtain ⟨Cn,hCn,hcore⟩ := exists_source_normal_block_bound d hd γ hγ τstar hτstar β hβ hβγ hhigh
  refine ⟨Cn,hCn,?_⟩
  intro G hG hCnG δ hδ
  obtain ⟨R,hR,hbound⟩ := hcore δ hδ.1 hδ.2
  refine ⟨R,hR,?_⟩
  intro L hL D N hτ A η hD hγη p ν r hr hrupper t c C CsA CmA CsC CmC i hCG
  have hL1 : 1 ≤ L := by linarith [hR.trans hL]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hδ1 : δ ∈ Ioc (0:ℝ) 1 := ⟨hδ.1,by linarith [hδ.2]⟩
  let χ (j : Fin (D.S.m i.1)) : ℕ := if pairIncoherent D ⟨i.1,j⟩ then 1 else 0
  let χn : ℕ := if normalIncoherent D i then 1 else 0
  have hP (j : Fin (D.S.m i.1)) :
      sourcePairEnvelope D L γ δ η β τstar C CsA CmA CsC CmC ⟨i.1,j⟩ ≤
      ENNReal.ofReal (G^2*δ⁻¹*L^(2*((d:ℝ)-γ)-(β/20)*(χ j:ℝ))) := by
    have hns := not_special_pair_of_normal D ⟨i.1,j⟩ i.2
    have hb := sourcePairEnvelope_le_ordinary_budget D hL1 hδ.1 hβ.le hG hCG
      γ η τstar CsA CmA CsC CmC ⟨i.1,j⟩ hns.1 hns.2
    by_cases hq : pairIncoherent D ⟨i.1,j⟩ <;> simpa [χ,hq] using hb
  have hG4 : Cn ≤ G^4 := hCnG.trans (by simpa using pow_le_pow_right₀ hG (by norm_num : 1 ≤ 4))
  have hcore' : linearFactorMass D L γ δ p ν r t c (L^(-β)) i.1 *
      normalFactorMass D L γ δ p ν r t (enlargedTimeLower D c (L^(-β))) (enlargedTimeUpper D c (L^(-β))) i ≤
      ENNReal.ofReal (G^4*δ^(-(4:ℝ)/2)*L^(4*((d:ℝ)-γ)-(β/20)*(χn:ℝ))) := by
    have hb := hbound L hL D N hτ A η hD hγη p ν r hr hrupper t c i
    have he : (β/20)*(χn:ℝ) = (if normalIncoherent D i then β/20 else 0) := by
      by_cases hq : normalIncoherent D i <;> simp [χn,hq]
    rw [he]
    norm_num only [show -(4:ℝ)/2 = -2 by norm_num]
    apply hb.trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hG4 (Real.rpow_nonneg hδ.1.le _))
      (Real.rpow_nonneg hLp.le _)
  have hb := core_mul_pair_arity_budget
    (fun j : Fin (D.S.m i.1) => sourcePairEnvelope D L γ δ η β τstar C CsA CmA CsC CmC ⟨i.1,j⟩)
    χ 4 (zero_le_one.trans hG) hδ.1 hLp hcore' hP
  have hn : 4+2*D.S.m i.1 = D.S.n i.1 := by simp [SumintShape.n,i.2]; omega
  have hc : (∑ j, χ j)+χn = blockDiscrepancy D i.1 := by
    simp only [blockDiscrepancy,dite_eq_left i.2]
    rfl
  have hexp : (4*((d:ℝ)-γ)-(β/20)*(χn:ℝ))+
      (((2*D.S.m i.1:ℕ):ℝ)*((d:ℝ)-γ)-(β/20)*((∑ j, χ j):ℝ)) =
      (D.S.n i.1:ℝ)*((d:ℝ)-γ)-(β/20)*(blockDiscrepancy D i.1:ℝ) := by
    rw [← hn,← hc]
    push_cast
    ring
  rw [Fintype.card_fin,hn,hexp] at hb
  apply le_trans (le_of_eq ?_) hb
  rw [normalMassInBlock,dite_eq_left i.2]
  ac_rfl

end WaveTurbulence.Sumint
