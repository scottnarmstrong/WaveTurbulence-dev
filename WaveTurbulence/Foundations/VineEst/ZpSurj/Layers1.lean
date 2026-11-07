/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Num1
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P1.Mix

/-! # ZP-SURJ: the numbers of the states of `Zp(A)` and `ZpLayers` -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
variable {kind : Bool}
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5B WaveTurbulence.Stage1 WaveTurbulence.LGSpine

variable {w : ℕ} {ι : Type*} {p : ℕ} {pstar : ι} {J : Set ι}
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

/-- The numbers `(L₃-side, L₄-side, L₂)` of an operation output, in terms of those of the start. -/
theorem op_numbers {ε : Bool} (con : LFConstruction (A.source pstar hcan hel htc hcc) ε) :
    (zpBranchQ (opOut A pstar hcan hel htc hcc con) pstar).2 = (zpBranchQ A pstar).2 ∧
    ((zpBranchQ (opOut A pstar hcan hel htc hcc con) pstar).1 = (zpBranchQ A pstar).1 ∧
      numR (opOut A pstar hcan hel htc hcc con) pstar = numR A pstar ∨
     (zpBranchQ (opOut A pstar hcan hel htc hcc con) pstar).1 = numR A pstar ∧
      numR (opOut A pstar hcan hel htc hcc con) pstar = (zpBranchQ A pstar).1) := by
  cases ε
  · obtain ⟨h1, h2⟩ := numbers_false A pstar hcan hel htc hcc con
    rw [h1, h2]; exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  · obtain ⟨h1, h2, h3⟩ := numbers_true A pstar hcan hel htc hcc con
    exact ⟨h2, Or.inr ⟨h1, h3⟩⟩

theorem zpPairQ_max (G : FamilyReconstruction w ι) (i : ι) :
    max (zpPairQ G i).1 (zpPairQ G i).2 = max (numR G i) (zpBranchQ G i).2 := by
  have h := zpQQ_eq G i
  unfold zpQQ at h
  by_cases hv : nuOf G i = -1
  · rw [if_pos hv] at h
    rw [h]
  · rw [if_neg hv] at h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    rw [← h1, ← h2, max_comm]

theorem zpQ4_eq : zpQ4 A pstar = min (max (numR A pstar) (zpBranchQ A pstar).2) (zpBranchQ A pstar).1 := by
  unfold zpQ4
  rw [zpPairQ_max]

theorem zpQ2_eq : zpQ2 A pstar = (zpBranchQ A pstar).2 := rfl

include hcan hel htc hcc

theorem zpLayers_of_start [DecidableEq ι] [Fintype ι] (hA : IsPrimeGarden A.skeleton)
    (sp0 : SplitAt A.skeleton A.family pstar J) : ZpLayers p kind J A sp0 hA := by
  have h1 := L2_le_q1 A pstar hcan hel htc hcc
  have h2 := L2_le_q2 A pstar hcan hel htc hcc
  have h3 := q1_le_p A pstar hcan hel htc hcc
  have h4 := q2_le_p A pstar hcan hel htc hcc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [zpQ2_eq, zpQ4_eq]
    exact le_min (le_max_right _ _) h2
  · rw [zpQ4_eq]
    exact (min_le_right _ _).trans h4
  · intro G hG
    have hb := (mem_zpFinset hA).1 hG
    obtain ⟨ε, con, he⟩ := classify A hcan hel htc hcc hA hb.batch
    rw [he, zpQQ_eq]
    obtain ⟨hL, hn⟩ := op_numbers A hcan hel htc hcc con
    rw [zpQ2_eq]
    rcases hn with ⟨-, hr⟩ | ⟨-, hr⟩
    · rw [hr, hL]; exact ⟨rfl, h1, h3⟩
    · rw [hr, hL]; exact ⟨rfl, h2, h4⟩
  · intro G hG
    have hb := (mem_zpFinset hA).1 hG
    obtain ⟨ε, con, he⟩ := classify A hcan hel htc hcc hA hb.batch
    rw [he]
    obtain ⟨hL, hn⟩ := op_numbers A hcan hel htc hcc con
    rw [zpQ2_eq]
    rcases hn with ⟨hr, -⟩ | ⟨hr, -⟩
    · rw [hr, hL]; exact ⟨rfl, h2⟩
    · rw [hr, hL]; exact ⟨rfl, h1⟩

end WaveTurbulence.ZpSurj

namespace WaveTurbulence.ZpSurj
variable {kind : Bool}
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5B

/-- **`hq2`** (V5 P4): the layer of the lower joint is at most the layer of the core of its partner's parent
(`sourceExpanded_parent_guard`, bridged through `inducedPrelayer = cll`). -/
theorem zpQ2_le_of_state {w : ℕ} {ι : Type*} {p : ℕ} {pstar : ι} (A : FamilyReconstruction w ι)
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
        ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).secondLeaf A.plain).toNode))) :
    zpQ2 A pstar ≤ stateLayer A (A.data.coreBranch A.plain (qrOf (A.family.placement pstar))).toNode := by
  have h := L2_le_q1 A pstar hcan hel htc hcc
  rw [numR_eq] at h
  rw [cl_eq_layerAt]
  exact h

end WaveTurbulence.ZpSurj
