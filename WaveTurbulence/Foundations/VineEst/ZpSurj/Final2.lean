/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Final1

/-! # ZP-SURJ: the carrier-side objects of a II-b state are coherent at `(L₄, L₂)` -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
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

theorem cross_numbers {ε : Bool} (con : LFConstruction (A.source pstar hcan hel htc hcc) ε)
    (con' : LFConstruction (A.source pstar hcan hel htc hcc) (!ε)) :
    (zpBranchQ (opOut A pstar hcan hel htc hcc con') pstar).1 = numR (opOut A pstar hcan hel htc hcc con) pstar ∧
    numR (opOut A pstar hcan hel htc hcc con') pstar = (zpBranchQ (opOut A pstar hcan hel htc hcc con) pstar).1 ∧
    (numR (opOut A pstar hcan hel htc hcc con) pstar = zpQ4 A pstar ∨
      (zpBranchQ (opOut A pstar hcan hel htc hcc con) pstar).1 = zpQ4 A pstar) := by
  have h1 := L2_le_q1 A pstar hcan hel htc hcc
  have hm := zpQ4_eq A (pstar := pstar)
  rw [max_eq_left h1] at hm
  cases ε
  · obtain ⟨a1, a2⟩ := numbers_false A pstar hcan hel htc hcc con
    obtain ⟨b1, -, b3⟩ := numbers_true A pstar hcan hel htc hcc con'
    rw [a1, a2, b1, b3]
    refine ⟨rfl, rfl, ?_⟩
    rw [hm]
    rcases le_total (numR A pstar) (zpBranchQ A pstar).1 with h | h
    · left; rw [min_eq_left h]
    · right; rw [min_eq_right h]
  · obtain ⟨a1, -, a3⟩ := numbers_true A pstar hcan hel htc hcc con
    obtain ⟨b1, b2⟩ := numbers_false A pstar hcan hel htc hcc con'
    rw [a1, a3, b1, b2]
    refine ⟨rfl, rfl, ?_⟩
    rw [hm]
    rcases le_total (numR A pstar) (zpBranchQ A pstar).1 with h | h
    · right; rw [min_eq_left h]
    · left; rw [min_eq_right h]

theorem carrier_coherent {ε : Bool} (con : LFConstruction (A.source pstar hcan hel htc hcc) ε)
    (hv : nuOf (opOut A pstar hcan hel htc hcc con) pstar = -1) (hn : NR A hcan hel htc hcc con) :
    IsCoherentCoupleAt p (zpQ4 A pstar) (zpBranchQ A pstar).2 con.newCouple (conLQ con) ∧
    IsCoherentTreeAt p (zpQ4 A pstar) (zpBranchQ A pstar).2 (conjChain con.newTree)
      (conjLayered (conLX con) (Equiv.refl (Fin 1))) := by
  obtain ⟨n0, n1, n2⟩ := hn
  obtain ⟨con', h1, h2, h3, h4⟩ := twin_con A hcan hel htc hcc con n0 n1 n2
  have hnat := nativeCoh_op A pstar hcan hel htc hcc con
  rw [zpData_op A hcan hel htc hcc con, sigStar_op A pstar hcan hel htc hcc con] at hnat
  have hnat' := nativeCoh_op A pstar hcan hel htc hcc con'
  rw [zpData_op A hcan hel htc hcc con', sigStar_op A pstar hcan hel htc hcc con'] at hnat'
  simp only at hnat hnat'
  obtain ⟨hGL, -⟩ := op_numbers A hcan hel htc hcc con
  obtain ⟨hGL', -⟩ := op_numbers A hcan hel htc hcc con'
  obtain ⟨c1, c2, c3⟩ := cross_numbers A hcan hel htc hcc con con'
  have hv' : nuOf (opOut A pstar hcan hel htc hcc con') pstar = 1 := by
    rw [nuOf_op A hcan hel htc hcc con', srcSign_not A hcan hel htc hcc ε, ← nuOf_op A hcan hel htc hcc con, hv]
    decide
  have pq := pairQ_neg (opOut A pstar hcan hel htc hcc con) pstar hv
  have pq' := pairQ_pos (opOut A pstar hcan hel htc hcc con') pstar hv'
  rw [pq, hGL] at hnat
  rw [pq', hGL'] at hnat'
  obtain ⟨CQ, CT⟩ := hnat
  obtain ⟨CQ', CT'⟩ := hnat'
  simp only at CQ CT CQ' CT'
  have CT2 := isCoherentTreeAt_conj (conjLayered_isConjugateBy (conLX con) (Equiv.refl (Fin 1))) CT
  rw [h4] at CT'
  rw [h2] at CT'
  refine ⟨?_, ?_⟩
  · rcases c3 with hm | hm
    · rw [← hm]; exact CQ
    · have := isCoherentCoupleAt_conj (conjLayered_isConjugateCouple (conLQ con')) CQ'
      rw [h3, conjLayered_invol _ (fun x => Equiv.swap_apply_self _ _ x), h1, conjCpl_conjCpl, c2, hm] at this
      exact this
  · rcases c3 with hm | hm
    · rw [c1] at CT'
      rw [← hm]
      exact CT'
    · rw [← hm]; exact CT2

end WaveTurbulence.ZpSurj
