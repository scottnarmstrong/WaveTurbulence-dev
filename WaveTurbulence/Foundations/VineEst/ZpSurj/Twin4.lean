/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Twin3

/-! # ZP-SURJ: the twin construction -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
variable {kind : Bool}
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5B WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.ConjCoh

variable {w : ℕ} {ι : Type*} {p : ℕ} {pstar : ι}
variable (A : FamilyReconstruction w ι)
  (hcan : CanonicalObject p kind A.layered)
  (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement pstar) (A.family.kind pstar)
    (A.family.atoms pstar) (A.family.upper pstar))
  (htc : CohOn A.layered ((A.data.tree (A.family.placement pstar).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement pstar).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement pstar).lower.toNode)))
  (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).secondLeaf A.plain).toNode)))

include hcan hel htc hcc

/-- Numerical facts about the base gardens. -/
theorem base_facts (ε : Bool) :
    (zpBranchQ (baseState A hcan hel htc hcc ε) pstar).2 = (zpBranchQ A pstar).2 ∧
    zpQ4 A pstar ≤ numR (baseState A hcan hel htc hcc ε) pstar ∧
    zpQ4 A pstar ≤ (zpBranchQ (baseState A hcan hel htc hcc ε) pstar).1 ∧
    (zpBranchQ A pstar).2 ≤ numR (baseState A hcan hel htc hcc ε) pstar := by
  have h1 := L2_le_q1 A pstar hcan hel htc hcc
  have h2 := L2_le_q2 A pstar hcan hel htc hcc
  have hm := zpQ4_eq A (pstar := pstar)
  have m1 : zpQ4 A pstar ≤ numR A pstar := by
    rw [hm]; exact (min_le_left _ _).trans (by rw [max_eq_left h1])
  have m2 : zpQ4 A pstar ≤ (zpBranchQ A pstar).1 := by rw [hm]; exact min_le_right _ _
  cases ε
  · obtain ⟨b1, b2⟩ := base_nums_false A hcan hel htc hcc
    rw [b1, b2]; exact ⟨rfl, m1, m2, h1⟩
  · obtain ⟨b1, b2, b3⟩ := base_nums_true A hcan hel htc hcc
    rw [b1, b2, b3]; exact ⟨rfl, m2, m1, h2⟩

theorem twin_con {ε : Bool} (con : LFConstruction (A.source pstar hcan hel htc hcc) ε)
    (hr0 : layerAt (conLQ con) ((0 : Fin 2), ([] : Path)) ≤ zpQ4 A pstar)
    (hr1 : layerAt (conLQ con) ((1 : Fin 2), ([] : Path)) ≤ zpQ4 A pstar)
    (hrT : layerAt (conLX con) ((0 : Fin 1), ([] : Path)) ≤ zpQ4 A pstar) :
    ∃ con' : LFConstruction (A.source pstar hcan hel htc hcc) (!ε),
      con'.newCouple = conjCpl con.newCouple ∧ con'.newTree = conjChain con.newTree ∧
      conLQ con' = conjLayered (conLQ con) (Equiv.swap (0 : Fin 2) 1) ∧
      conLX con' = conjLayered (conLX con) (Equiv.refl (Fin 1)) := by
  have hnat := nativeCoh_op A pstar hcan hel htc hcc con
  rw [zpData_op A hcan hel htc hcc con, sigStar_op A pstar hcan hel htc hcc con] at hnat
  obtain ⟨hNC, hNT⟩ := hnat
  simp only at hNC hNT
  have hC' := isCoherentCoupleAt_conj (conjLayered_isConjugateCouple (conLQ con)) hNC
  have hT' := isCoherentTreeAt_conj (conjLayered_isConjugateBy (conLX con) (Equiv.refl (Fin 1))) hNT
  have hpatN := pattern_of_coherentCouple hNC
  obtain ⟨R0, R1⟩ := layerPatternN_root_le hpatN
  obtain ⟨hGL, hGn⟩ := op_numbers A hcan hel htc hcc con
  obtain ⟨bL, bm1, bm2, bL1⟩ := base_facts A hcan hel htc hcc (!ε)
  have hB := base_pair_parents (p := p) A hcan hel htc hcc (!ε)
  have hB2 := base_branch_parents (p := p) A hcan hel htc hcc (!ε)
  have hνB := nuOf_base A hcan hel htc hcc (!ε)
  generalize baseState A hcan hel htc hcc (!ε) = B' at bL bm1 bm2 bL1 hB hB2 hνB
  have hνG := nuOf_op A hcan hel htc hcc con
  have hνn : nuOf B' pstar = - nuOf (opOut A pstar hcan hel htc hcc con) pstar := by
    rw [hνB, hνG]; exact srcSign_not A hcan hel htc hcc ε
  have h1 := L2_le_q1 A pstar hcan hel htc hcc
  have h2 := L2_le_q2 A pstar hcan hel htc hcc
  have hGnum : (zpBranchQ A pstar).2 ≤ numR (opOut A pstar hcan hel htc hcc con) pstar := by
    rcases hGn with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> assumption
  have hconjQ := conjLayered_isConjugateCouple (conLQ con)
  have hconjT := conjLayered_isConjugateBy (conLX con) (Equiv.refl (Fin 1))
  have hc0 : layerAt (conjLayered (conLQ con) (Equiv.swap (0 : Fin 2) 1)) ((0 : Fin 2), ([] : Path)) =
      layerAt (conLQ con) ((1 : Fin 2), ([] : Path)) := by
    have := layerAt_conj hconjQ ((1 : Fin 2), ([] : Path))
    rw [phi_swap_one] at this; exact this
  have hc1 : layerAt (conjLayered (conLQ con) (Equiv.swap (0 : Fin 2) 1)) ((1 : Fin 2), ([] : Path)) =
      layerAt (conLQ con) ((0 : Fin 2), ([] : Path)) := by
    have := layerAt_conj hconjQ ((0 : Fin 2), ([] : Path))
    rw [phi_swap_zero] at this; exact this
  have hcT : layerAt (conjLayered (conLX con) (Equiv.refl (Fin 1))) ((0 : Fin 1), ([] : Path)) =
      layerAt (conLX con) ((0 : Fin 1), ([] : Path)) := layerAt_conj hconjT ((0 : Fin 1), ([] : Path))
  have hBa := congrArg Prod.fst hB
  have hBb := congrArg Prod.snd hB
  simp only at hBa hBb
  have hD : ExcDatum (A.source pstar hcan hel htc hcc) (!ε) (conjCpl con.newCouple) (conjChain con.newTree)
      (conjLayered (conLQ con) (Equiv.swap (0 : Fin 2) 1)) (conjLayered (conLX con) (Equiv.refl (Fin 1))) := by
    refine datum_of_coherent hC' hT' ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hBa, hBb]
      rcases nuOf_cases (opOut A pstar hcan hel htc hcc con) pstar with hv | hv
      · have hv' : nuOf B' pstar = -1 := by rw [hνn, hv]; try decide
        rw [pairQ_pos (opOut A pstar hcan hel htc hcc con) pstar hv, pairQ_neg B' pstar hv', hGL, bL]
        simp only
        rw [min_eq_right bL1, min_eq_right hGnum]
      · have hv' : nuOf B' pstar = 1 := by
          rw [hνn, hv]; rfl
        rw [pairQ_neg (opOut A pstar hcan hel htc hcc con) pstar hv, pairQ_pos B' pstar hv', hGL, bL]
        simp only
        rw [min_eq_left bL1, min_eq_left hGnum]
    · rw [hBa, hc0]
      rcases nuOf_cases (opOut A pstar hcan hel htc hcc con) pstar with hv | hv
      · have hv' : nuOf B' pstar = -1 := by rw [hνn, hv]; try decide
        rw [pairQ_neg B' pstar hv']
        exact hr1.trans bm1
      · have hv' : nuOf B' pstar = 1 := by rw [hνn, hv]; try decide
        rw [pairQ_pos B' pstar hv', bL]
        have := R1
        rw [pairQ_neg (opOut A pstar hcan hel htc hcc con) pstar hv, hGL] at this
        exact this
    · rw [hBb, hc1]
      rcases nuOf_cases (opOut A pstar hcan hel htc hcc con) pstar with hv | hv
      · have hv' : nuOf B' pstar = -1 := by rw [hνn, hv]; try decide
        rw [pairQ_neg B' pstar hv', bL]
        have := R0
        rw [pairQ_pos (opOut A pstar hcan hel htc hcc con) pstar hv, hGL] at this
        exact this
      · have hv' : nuOf B' pstar = 1 := by rw [hνn, hv]; try decide
        rw [pairQ_pos B' pstar hv']
        exact hr0.trans bm1
    · have e : parAt ((A.source pstar hcan hel htc hcc).base (!ε)) p (tA (A.source pstar hcan hel htc hcc) (!ε)) =
          (zpBranchQ B' pstar).1 := congrArg Prod.fst hB2
      rw [hcT, e]; exact hrT.trans bm2
    · show -(conLX con).garden.sig 0 = _
      rw [conLX_sig con, srcSign_not A hcan hel htc hcc ε]
    · have e : layerAt ((A.source pstar hcan hel htc hcc).base (!ε)) (tA (A.source pstar hcan hel htc hcc) (!ε)) =
          (zpBranchQ B' pstar).2 := congrArg Prod.snd hB2
      rw [e, hGL, bL]
    · rw [size_conjChain, size_conjCpl]; exact con.combinedOrder
  have hc : srcRaw (p := p) (pstar := pstar) A =
      topBranchCount (conjLayered (conLX con) (Equiv.refl (Fin 1))) p +
        topBranchCount (conjLayered (conLQ con) (Equiv.swap (0 : Fin 2) 1)) p := by
    rw [topBranchCount_conj hconjT, topBranchCount_conj hconjQ]
    exact srcRaw_eq_con A hcan hel htc hcc con
  exact state_of_datum A hcan hel htc hcc hD hc

end WaveTurbulence.ZpSurj
