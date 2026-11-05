/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistOtherPlacement

/-! # The full local port permutation of a unit twist

TARGET twistexplain (a): at the lower atom the parent and retained ports
are exchanged, while the two free child ports are exchanged. This is a
permutation of the four ordered incidence positions.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- The two disjoint transpositions on lower-atom incidence ports. -/
@[expose] def switchPort (keep : Fin 3) : Equiv.Perm (Fin 4) :=
  (Equiv.swap 0 keep.succ).trans (Equiv.swap (1 : Fin 3).succ ((if keep = 0 then (2 : Fin 3) else 0)).succ)

/-- The old parent port becomes the retained child port. -/
theorem switchPort_zero (keep : Fin 3) (ho : keep ≠ 1) : switchPort keep 0 = keep.succ := by
  fin_cases keep <;> simp_all [switchPort,Equiv.swap_apply_def]

/-- The retained child port becomes the parent port. -/
theorem switchPort_keep (keep : Fin 3) (ho : keep ≠ 1) : switchPort keep keep.succ = 0 := by
  fin_cases keep <;> simp_all [switchPort,Equiv.swap_apply_def]

/-- Each free child port follows the actual free-subtree exchange. -/
theorem switchPort_free (keep i : Fin 3) (ho : keep ≠ 1) (hi : i ≠ keep) :
    switchPort keep i.succ = (freeSwap keep i).succ := by
  fin_cases keep <;> fin_cases i <;> simp_all [switchPort,freeSwap,Equiv.swap_apply_def]

variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The retained LP incidence becomes the new lower parent incidence. -/
theorem retainedLP_twisted_position :
    Mole.dartPosition (unitTwistGarden G P) (twistDartEquiv G P (retainedLP G P)) = 0 := by
  change Mole.dartPosition (unitTwistGarden G P)
    (naiveDartEquiv G P (exceptionalDartSwap G P (retainedLP G P))) = 0
  rw [exceptionalDartSwap_retainedLP]
  rfl

/-- Every incidence position follows the explicit permutation at the lower atom. -/
theorem twistDartEquiv_position (x : GardenDart G) :
    Mole.dartPosition (unitTwistGarden G P) (twistDartEquiv G P x) =
      if G.molecule.atom x = P.lower then switchPort P.keep (Mole.dartPosition G x) else Mole.dartPosition G x := by
  classical
  by_cases hx : G.molecule.atom x = P.lower
  · simp only [hx,ite_true]
    cases x with
    | inl c =>
      obtain ⟨c,side⟩ := c
      cases side
      · have hc : c = ⟨P.lower,P.nonroot⟩ := Subtype.ext hx
        subst c
        exact (lowerPC_twisted_position G P).trans (switchPort_zero P.keep P.outer).symm
      · have hc : c.1 ≠ P.lower := by
          intro he
          have hp : GNode.parent c.1.toNode c.2 = GNode.parent P.lower.toNode P.nonroot :=
            Subtype.ext (congrArg (fun b : GBranch G.tree => (b.1.1,b.1.2.dropLast)) he)
          exact branch_ne_parent G P.lower P.nonroot (hp.symm.trans hx).symm
        have hp : GNode.parent c.1.toNode c.2 = P.lower := hx
        have hch := (Mole.parent_child_eq_node c.1.toNode c.2).symm
        have hct := branch_child_transport G P hch hc
        have hv := congrArg Subtype.val hp
        have hslot : exchangeChildSlot P.lower.1 P.keep (GNode.parent c.1.toNode c.2).1
            (c.1.1.2.getLast c.2) = freeSwap P.keep (c.1.1.2.getLast c.2) := by simp [exchangeChildSlot,hv]
        have hi : c.1.1.2.getLast c.2 ≠ P.keep := by
          intro he
          have hn : c.1.toNode = P.retained.toNode := by
            exact hch.trans ((congrArg (fun p : GBranch G.tree => p.child (c.1.1.2.getLast c.2)) hp).trans
              ((congrArg P.lower.child he).trans P.child.symm))
          exact Mole.branch_toNode_ne_leaf c.1 P.retained hn
        have he : Mole.dartPosition (unitTwistGarden G P) (twistDartEquiv G P (.inl (c,true))) =
            (freeSwap P.keep (c.1.1.2.getLast c.2)).succ := by
          change Mole.dartPosition (unitTwistGarden G P) (naiveDartEquiv G P (exceptionalDartSwap G P (.inl (c,true)))) = _
          rw [exceptionalDartSwap_otherPC G P c hc true]
          exact congrArg Fin.succ ((last_eq_of_child _ hct).trans hslot)
        exact he.trans (switchPort_free P.keep _ P.outer hi).symm
    | inr l =>
      by_cases hl : l.1 = P.retained
      · have he : (.inr l : GardenDart G) = retainedLP G P := congrArg Sum.inr (Subtype.ext hl)
        exact (congrArg (fun x => Mole.dartPosition (unitTwistGarden G P) (twistDartEquiv G P x)) he).trans
          ((retainedLP_twisted_position G P).trans ((switchPort_keep P.keep P.outer).symm.trans
            (congrArg (switchPort P.keep) ((retainedLP_position G P).symm.trans (congrArg (Mole.dartPosition G) he.symm)))))
      · have hp : GNode.parent l.1.toNode l.2.2.1 = P.lower := hx
        have hpair : l.1 ≠ G.pair P.retained := by
          intro he
          have hh := leaf_parent_congr G l.2.2.1 P.paired_nonroot he
          exact placement_paired_parent_ne G P (hh.symm.trans hp)
        have hch := (Mole.parent_child_eq_node l.1.toNode l.2.2.1).symm
        have hct := leaf_child_transport G P hch hpair
        have hv := congrArg Subtype.val hp
        have hslot : exchangeChildSlot P.lower.1 P.keep (GNode.parent l.1.toNode l.2.2.1).1
            (l.1.1.2.getLast l.2.2.1) = freeSwap P.keep (l.1.1.2.getLast l.2.2.1) := by simp [exchangeChildSlot,hv]
        have hi : l.1.1.2.getLast l.2.2.1 ≠ P.keep := by
          intro he
          apply hl
          apply Mole.leaf_toNode_injective
          exact hch.trans ((congrArg (fun p : GBranch G.tree => p.child (l.1.1.2.getLast l.2.2.1)) hp).trans
            ((congrArg P.lower.child he).trans P.child.symm))
        have he : Mole.dartPosition (unitTwistGarden G P) (twistDartEquiv G P (.inr l)) =
            (freeSwap P.keep (l.1.1.2.getLast l.2.2.1)).succ := by
          change Mole.dartPosition (unitTwistGarden G P) (naiveDartEquiv G P (exceptionalDartSwap G P (.inr l))) = _
          rw [exceptionalDartSwap_otherLP G P l hl hpair]
          exact congrArg Fin.succ ((last_eq_of_child _ hct).trans hslot)
        exact he.trans (switchPort_free P.keep _ P.outer hi).symm
  · simp only [hx,ite_false]
    exact twistDartEquiv_position_other G P x hx

end WaveTurbulence.Twist
