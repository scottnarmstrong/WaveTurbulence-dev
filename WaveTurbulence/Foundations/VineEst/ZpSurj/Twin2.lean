/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Twin1

/-! # ZP-SURJ: numbers of the base gardens, signs and counts of the start state -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
variable {kind : Bool}
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5B WaveTurbulence.Stage1 WaveTurbulence.LGSpine

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

theorem srcSign_false : srcSign (A.source pstar hcan hel htc hcc) false = nuOf A pstar := rfl

theorem srcSign_true : srcSign (A.source pstar hcan hel htc hcc) true = -nuOf A pstar := by
  have h := (coreBranchEquiv_sign A.skeleton (A.family.placement pstar) (A.family.placement pstar).lower).trans
    (if_pos rfl)
  exact h

theorem srcSign_not (ε : Bool) :
    srcSign (A.source pstar hcan hel htc hcc) (!ε) = -srcSign (A.source pstar hcan hel htc hcc) ε := by
  cases ε
  · show srcSign _ true = -srcSign _ false
    rw [srcSign_true, srcSign_false]
  · show srcSign _ false = -srcSign _ true
    rw [srcSign_false, srcSign_true]; simp

theorem base_nums_false :
    zpBranchQ (baseState A hcan hel htc hcc false) pstar = zpBranchQ A pstar ∧
      numR (baseState A hcan hel htc hcc false) pstar = numR A pstar :=
  numbers_false_gen (base_pin A hcan hel htc hcc false) rfl

theorem base_nums_true :
    (zpBranchQ (baseState A hcan hel htc hcc true) pstar).1 = numR A pstar ∧
      (zpBranchQ (baseState A hcan hel htc hcc true) pstar).2 = (zpBranchQ A pstar).2 ∧
      numR (baseState A hcan hel htc hcc true) pstar = (zpBranchQ A pstar).1 :=
  numbers_true_gen (base_pin A hcan hel htc hcc true) rfl

/-- The raw layer-`p` count of the start state's exceptional rows. -/
@[expose] noncomputable def srcRaw : ℕ :=
  rawTreeLayerCount A.layered A.data A.plain p (A.family.placement pstar).lower +
    rawCoupleLayerCount A.layered A.data A.plain p
      (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)

theorem srcRaw_eq_start :
    srcRaw (p := p) (pstar := pstar) A = topBranchCount (sigStar A pstar).2.2 p + topBranchCount (sigStar A pstar).2.1 p := by
  have h1 := raw_tree_bridge A.data A.plain (stateLayer A) (stateLayer_isLayering A) p (A.family.placement pstar).lower
  have h2 := raw_couple_bridge A.data A.plain (stateLayer A) (stateLayer_isLayering A) p
    (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)
  rw [stateLayer_spec A] at h1 h2
  unfold srcRaw
  rw [h1, h2]
  rfl

theorem srcRaw_eq_con {ε : Bool} (con : LFConstruction (A.source pstar hcan hel htc hcc) ε) :
    srcRaw (p := p) (pstar := pstar) A = topBranchCount (conLX con) p + topBranchCount (conLQ con) p := by
  have h := con.combinedTopCount
  have h1 := raw_tree_bridge con.data ((A.source pstar hcan hel htc hcc).chosen_plain ε) con.outLayer
    con.out_isLayering p ((A.source pstar hcan hel htc hcc).branches ε (A.family.placement pstar).lower)
  have h2 := raw_couple_bridge con.data ((A.source pstar hcan hel htc hcc).chosen_plain ε) con.outLayer
    con.out_isLayering p ((A.source pstar hcan hel htc hcc).pairs ε (A.source pstar hcan hel htc hcc).exceptional)
  unfold srcRaw
  exact h.trans (congrArg₂ (· + ·) h1 h2)

end WaveTurbulence.ZpSurj
