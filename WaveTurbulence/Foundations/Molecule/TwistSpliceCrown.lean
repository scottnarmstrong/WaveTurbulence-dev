/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistExcludedSubtree
public import WaveTurbulence.Foundations.Molecule.SpliceCrownAssembly

/-! # The exact ordered CL splice crown is unchanged by a unit twist -/

public section
namespace WaveTurbulence.Twist
open TTree

/-- The two free child indices are exchanged. -/
theorem freeSwap_middle (keep : Fin 3) (hk : keep ≠ 1) : freeSwap keep 1 = Mole.otherOuterChild keep := by
  fin_cases keep <;> simp_all [freeSwap,Mole.otherOuterChild]

/-- The other free child moves into the middle position. -/
theorem freeSwap_other (keep : Fin 3) (hk : keep ≠ 1) : freeSwap keep (Mole.otherOuterChild keep) = 1 := by
  have hh := freeSwap_involutive keep 1
  rw [freeSwap_middle keep hk] at hh
  exact hh

variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The exact source same-sign flag is reversed. -/
theorem clSameSign_unitTwist {a : GBranch G.tree} (ha : a ≠ P.lower) :
    Mole.clSameSign (G := unitTwistGarden G P) (coreBranchEquiv G P a) (coreBranchEquiv G P P.lower) = !Mole.clSameSign (G := G) a P.lower := by
  have hA := (coreBranchEquiv_sign G P a).trans (ite_eq_right ha)
  have hB := (coreBranchEquiv_sign G P P.lower).trans (ite_eq_left rfl)
  change decide ((unitTwistGarden G P).sign (coreBranchEquiv G P a).toNode =
      (unitTwistGarden G P).sign (coreBranchEquiv G P P.lower).toNode) =
    !decide (G.sign a.toNode = G.sign P.lower.toNode)
  apply (congrArg₂ (fun x y : ℤˣ => decide (x = y)) hA hB).trans
  rcases Int.units_eq_one_or (G.sign a.toNode) with hsa | hsa <;>
    rcases Int.units_eq_one_or (G.sign P.lower.toNode) with hsb | hsb <;> simp [hsa,hsb]

variable {S : Finset (GBranch G.tree)} {a : GBranch G.tree}

/-- The old source boundary-root data, using the actual current block. -/
@[expose] noncomputable def originalSpliceBoundary (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (D : Mole.CLSpliceSlots G S a P.lower) :=
  Mole.clSpliceBoundary hB hCL D

/-- The actual source boundary-root data of the transported CL block. -/
@[expose] noncomputable def twistedSpliceBoundary (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P)
    (D : Mole.CLSpliceSlots G S a P.lower) :=
  Mole.clSpliceBoundary (isBlock_twistedAtoms G P hB)
    (clParentPattern_twistedAtoms G P hB hCL hP) (twistedSpliceSlots G P hB hCL hP D)

/-- All three ordered retained subtree pieces assemble to exactly the same literal crown. -/
theorem unitTwist_spliceCrown (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P)
    (D : Mole.CLSpliceSlots G S a P.lower) :
    Mole.spliceCrown (unitTwistGarden G P) (twistedSpliceBoundary G P hB hCL hP D).node =
      Mole.spliceCrown G (originalSpliceBoundary G P hB hCL D).node := by
  have hold := clSpliceCrown_assembly G hB hCL D
  have hnew := clSpliceCrown_assembly (unitTwistGarden G P)
    (isBlock_twistedAtoms G P hB)
    (clParentPattern_twistedAtoms G P hB hCL hP) (twistedSpliceSlots G P hB hCL hP D)
  have hupper := excluded_subtree_unchanged G P hB hCL hP D
  have hm := lower_child_subtree G P 1
  have ho := lower_child_subtree G P (Mole.otherOuterChild P.keep)
  have hmid := congrArg (fun i => Mole.spliceNodeSubtree (unitTwistGarden G P) ((coreBranchEquiv G P P.lower).child i))
    (freeSwap_middle P.keep P.outer)
  have hother := congrArg (fun i => Mole.spliceNodeSubtree (unitTwistGarden G P) ((coreBranchEquiv G P P.lower).child i))
    (freeSwap_other P.keep P.outer)
  have hmid' := hother.symm.trans ho
  have hother' := hmid.symm.trans hm
  have hk := spliceSlots_kept G P hP D
  refine hnew.trans (Eq.trans ?_ hold.symm)
  change assembleSpliceCrown D.excluded (Mole.clSameSign (G := unitTwistGarden G P) (coreBranchEquiv G P a) (coreBranchEquiv G P P.lower))
    (Mole.spliceNodeSubtree (unitTwistGarden G P) ((coreBranchEquiv G P a).child D.excluded))
    (Mole.spliceNodeSubtree (unitTwistGarden G P) ((coreBranchEquiv G P P.lower).child 1))
    (Mole.spliceNodeSubtree (unitTwistGarden G P) ((coreBranchEquiv G P P.lower).child (Mole.otherOuterChild P.keep))) = _
  have he := congrArg (fun k => Mole.spliceNodeSubtree G (P.lower.child (Mole.otherOuterChild k))) hk
  calc
    _ = assembleSpliceCrown D.excluded (!Mole.clSameSign (G := G) a P.lower)
        (Mole.spliceNodeSubtree G (a.child D.excluded))
        (Mole.spliceNodeSubtree G (P.lower.child (Mole.otherOuterChild P.keep)))
        (Mole.spliceNodeSubtree G (P.lower.child 1)) := by
      exact assembleSpliceCrown_congr D.excluded (clSameSign_unitTwist G P hB.2.2.2.1)
        hupper hmid' hother'
    _ = _ := (assembleSpliceCrown_swap _ _ _ _ _).trans (congrArg
      (assembleSpliceCrown D.excluded (Mole.clSameSign (G := G) a P.lower)
        (Mole.spliceNodeSubtree G (a.child D.excluded)) (Mole.spliceNodeSubtree G (P.lower.child 1))) he.symm)

end WaveTurbulence.Twist
