/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistOrdinaryPositions
public import WaveTurbulence.Foundations.Molecule.IsoIncidencePositions

/-! # The designated source CL block survives the actual unit twist

The connected block and expanded-template vine predicates transport by
isomorphism. The upper excluded slot is unchanged, and the retained
lower slot is the same outer slot after the PC/LP exchange.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The literal source vine, including all template multiplicities, is preserved. -/
theorem isVine_twistedAtoms {X : VineType} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hV : G.molecule.IsVine X S a b) :
    (unitTwistGarden G P).molecule.IsVine X (twistedAtoms G P S) (coreBranchEquiv G P a) (coreBranchEquiv G P b) :=
  iso_isVine G (unitTwistGarden G P) (unitTwistDirectedIso G P) hV

/-- Internal child and parent positions of every ordinary atom are unchanged. -/
theorem internalPositions_twist_other (S : Finset (GBranch G.tree)) (v : GBranch G.tree)
    (hv : v ≠ P.lower) (i : Fin 4) :
    i ∈ Mole.internalPositions (unitTwistGarden G P) (twistedAtoms G P S) (coreBranchEquiv G P v) ↔
      i ∈ Mole.internalPositions G S v :=
  iso_internalPositions_at G (unitTwistGarden G P) (unitTwistDirectedIso G P) S v
    (fun x hx => twistDartEquiv_position_other G P x (fun he => hv (hx.symm.trans he))) i

/-- The actual retained LP incidence occupies the retained child slot. -/
theorem retainedLP_position : Mole.dartPosition G (retainedLP G P) = P.keep.succ :=
  congrArg Fin.succ (last_eq_of_child (retained_nonroot G P) P.child)

/-- Designated internal-slot membership identifies the selected old u0 parent. -/
theorem placement_paired_parent_mem {S : Finset (GBranch G.tree)}
    (hP : IsPlacementAt G S P.lower P) : GNode.parent (G.pair P.retained).toNode P.paired_nonroot ∈ S := by
  have hi := (hP.2 P.keep).mpr rfl
  obtain ⟨x,ha,hg,hpos⟩ := (Mole.mem_internalPositions G).mp hi
  have he : x = retainedLP G P := Mole.atom_position_injective G
    (Prod.ext (ha.trans (retained_parent G P).symm) (hpos.trans (retainedLP_position G P).symm))
  subst x
  exact hg.2

/-- The actual twisted group is still CL with the same ordered upper/lower joints. -/
theorem clParentPattern_twistedAtoms {S : Finset (GBranch G.tree)} {a : GBranch G.tree}
    (hB : G.molecule.IsBlock S a P.lower) (hCL : Mole.CLParentPattern G S a P.lower)
    (hP : IsPlacementAt G S P.lower P) :
    Mole.CLParentPattern (unitTwistGarden G P) (twistedAtoms G P S)
      (coreBranchEquiv G P a) (coreBranchEquiv G P P.lower) := by
  constructor
  · intro ha
    have hv := (mem_twistedAtoms G P S a).mpr hB.2.1
    have hz := (Mole.zero_mem_internalPositions (unitTwistGarden G P) hv).mpr ha
    have hzold := (internalPositions_twist_other G P S a hB.2.2.2.1 0).mp hz
    exact hCL.1 ((Mole.zero_mem_internalPositions G hB.2.1).mp hzold)
  · refine ⟨(coreBranchEquiv_nonroot G P P.lower).mpr P.nonroot,?_⟩
    exact (lower_new_parent G P).symm ▸
      (mem_twistedAtoms G P S _).mpr (placement_paired_parent_mem G P hP)

/-- The old lower parent incidence becomes the retained child incidence at the new lower atom. -/
theorem lowerPC_twisted_position :
    Mole.dartPosition (unitTwistGarden G P) (twistDartEquiv G P (lowerPC G P false)) = P.keep.succ := by
  change Mole.dartPosition (unitTwistGarden G P)
    (naiveDartEquiv G P (exceptionalDartSwap G P (lowerPC G P false))) = _
  rw [exceptionalDartSwap_lowerPC]
  change ((coreLeafEquiv G P P.retained).1.2.getLast
    ((coreLeafEquiv_nonroot G P P.retained).mpr (retained_nonroot G P))).succ = _
  exact congrArg Fin.succ (last_eq_of_child _ (reversePlacement G P).child)

end WaveTurbulence.Twist
