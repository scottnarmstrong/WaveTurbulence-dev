/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Twin2

/-! # ZP-SURJ: the native data of an operation output as a tuple; pair parents by sign -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
variable {kind : Bool}
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5B WaveTurbulence.Stage1 WaveTurbulence.LGSpine

variable {w : ℕ} {ι : Type*} {p : ℕ}

open Classical in
theorem pairQ_neg (B : FamilyReconstruction w ι) (i : ι) (h : nuOf B i = -1) :
    zpPairQ B i = (numR B i, (zpBranchQ B i).2) := by
  have := zpQQ_eq B i
  unfold zpQQ at this
  rwa [if_pos h] at this

open Classical in
theorem pairQ_pos (B : FamilyReconstruction w ι) (i : ι) (h : nuOf B i = 1) :
    zpPairQ B i = ((zpBranchQ B i).2, numR B i) := by
  have h' : ¬ nuOf B i = -1 := by rw [h]; decide
  have := zpQQ_eq B i
  unfold zpQQ at this
  rw [if_neg h'] at this
  have h1 := congrArg Prod.fst this
  have h2 := congrArg Prod.snd this
  simp only at h1 h2
  exact Prod.ext h2 h1

theorem nuOf_cases (B : FamilyReconstruction w ι) (i : ι) : nuOf B i = 1 ∨ nuOf B i = -1 :=
  Int.units_eq_one_or _

variable {pstar : ι}
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
  {ε : Bool} (con : LFConstruction (A.source pstar hcan hel htc hcc) ε)

theorem zpData_op : zpData (opOut A pstar hcan hel htc hcc con) pstar =
    (con.newCouple, con.newTree, conLQ con, conLX con) := by
  have hq := op_pair_eq A pstar hcan hel htc hcc con
  have hl := op_lower_eq A pstar hcan hel htc hcc con
  have h1 : con.data.couple (chosenPairEquiv A.skeleton (A.family.placement pstar) A.plain ε
      (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)) = con.newCouple :=
    Function.update_self _ _ _
  have h2 : con.data.tree (chosenBranchEquiv A.skeleton (A.family.placement pstar) ε
      (A.family.placement pstar).lower) = con.newTree := Function.update_self _ _ _
  have hs := sigStar_op A pstar hcan hel htc hcc con
  unfold zpData
  rw [hs]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext rfl rfl))
  · show con.data.couple _ = _
    rw [hq]; exact h1
  · show con.data.tree _ = _
    rw [hl]; exact h2

theorem nuOf_op : nuOf (opOut A pstar hcan hel htc hcc con) pstar = srcSign (A.source pstar hcan hel htc hcc) ε := by
  unfold nuOf
  rw [sigStar_op]
  rfl

theorem nuOf_base (ε : Bool) :
    nuOf (baseState A hcan hel htc hcc ε) pstar = srcSign (A.source pstar hcan hel htc hcc) ε := by
  have e := chosenState_lower_eq (D := (A.source pstar hcan hel htc hcc).baseData ε)
    (L := (A.source pstar hcan hel htc hcc).base ε) (hd := (A.source pstar hcan hel htc hcc).base_decodes ε) A pstar
  unfold nuOf sigStar baseState
  dsimp only
  rw [e]
  rfl

end WaveTurbulence.ZpSurj
