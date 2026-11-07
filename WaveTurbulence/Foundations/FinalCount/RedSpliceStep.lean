/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CLCN
public import WaveTurbulence.Foundations.FinalCount.RedSpliceContract
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): the data of one CL splice step

For a (CL) block `S` with upper joint `a` of a garden `G`, `clSplicedGarden` (CLCN, TARGET
`block_clcn` (2)) is the spliced garden.  This file extracts, once and for all, the old-name data of
a splice: the injections `stepB` (new branch to old branch) and `stepD` (new dart to old dart), with
ranges, atoms, mates, orientations and parents, all in terms of the retraction `rep S a` (a block atom goes
to the crown `a`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open TTree Finset WaveTurbulence WaveTurbulence.Mole

variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- Retraction of the block `S` onto its crown `a`. -/
@[expose] noncomputable def rep (S : Finset (GBranch G.tree)) (a v : GBranch G.tree) : GBranch G.tree := by
  classical exact if v ∈ S then a else v

theorem rep_of_mem {v : GBranch G.tree} (h : v ∈ S) : rep S a v = a := by
  classical simp [rep, h]

theorem rep_of_notMem {v : GBranch G.tree} (h : v ∉ S) : rep S a v = v := by
  classical simp [rep, h]

theorem eq_rep_of_contract (ha : a ∈ S) {v w' : GBranch G.tree} (hv : v ∉ S ∨ v = a)
    (h : contractVertex S v = contractVertex S w') : v = rep S a w' := by
  by_cases hw : w' ∈ S
  · rw [rep_of_mem hw]
    rcases hv with hv | hv
    · exfalso
      rw [(contractVertex_eq_none S w').mpr hw] at h
      exact hv ((contractVertex_eq_none S v).mp h)
    · exact hv
  · rw [rep_of_notMem hw]
    rcases hv with hv | hv
    · exact contractVertex_outside_injective hv hw h
    · exfalso
      rw [hv, (contractVertex_eq_none S a).mpr ha] at h
      exact hw ((contractVertex_eq_none S w').mp h.symm)

variable (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b) (D : CLSpliceSlots G S a b)

/-- New branch to old branch (the crown keeps the name `a`). -/
@[expose] noncomputable def stepB (c : GBranch (clSplicedGardenOfSlots hB hCL D).tree) : GBranch G.tree :=
  (clSplicedBranchNameEquiv hB hCL D c).1

/-- New dart to old dart. -/
@[expose] noncomputable def stepD (x : GardenDart (clSplicedGardenOfSlots hB hCL D)) : GardenDart G :=
  (clSplicedDartEquiv hB hCL D x).1

theorem stepB_inj : Function.Injective (stepB hB hCL D) := fun _ _ h =>
  (clSplicedBranchNameEquiv hB hCL D).injective (Subtype.ext h)

theorem stepD_inj : Function.Injective (stepD hB hCL D) := fun _ _ h =>
  (clSplicedDartEquiv hB hCL D).injective (Subtype.ext h)

theorem stepB_mem (c) : stepB hB hCL D c ∉ S ∨ stepB hB hCL D c = a :=
  (clSplicedBranchNameEquiv hB hCL D c).2

theorem exists_stepB {v : GBranch G.tree} (hv : v ∉ S ∨ v = a) : ∃ c, stepB hB hCL D c = v :=
  ⟨(clSplicedBranchNameEquiv hB hCL D).symm ⟨v, hv⟩, by
    simp [stepB]⟩

theorem stepD_notInGroup (y) : ¬ G.molecule.InGroup S (stepD hB hCL D y) :=
  (clSplicedDartEquiv hB hCL D y).2

theorem exists_stepD {x : GardenDart G} (hx : ¬ G.molecule.InGroup S x) : ∃ y, stepD hB hCL D y = x :=
  ⟨(clSplicedDartEquiv hB hCL D).symm ⟨x, hx⟩, by simp [stepD]⟩

theorem stepD_mate (y) :
    stepD hB hCL D ((clSplicedGardenOfSlots hB hCL D).molecule.mate y) = G.molecule.mate (stepD hB hCL D y) := by
  have := clSplicedDartEquiv_mate hB hCL D y
  exact (congrArg Subtype.val this).symm

theorem stepD_out (y) :
    G.molecule.out (stepD hB hCL D y) = (clSplicedGardenOfSlots hB hCL D).molecule.out y :=
  clSplicedDartEquiv_out hB hCL D y

theorem stepB_atom (y) :
    stepB hB hCL D ((clSplicedGardenOfSlots hB hCL D).molecule.atom y) =
      rep S a (G.molecule.atom (stepD hB hCL D y)) := by
  apply eq_rep_of_contract hB.2.1 (stepB_mem hB hCL D _)
  have h1 := clSplicedBranchName_contract hB hCL D ((clSplicedGardenOfSlots hB hCL D).molecule.atom y)
  have h2 := clSplicedDartEquiv_atom hB hCL D y
  change contractVertex S (clSplicedBranchNameEquiv hB hCL D _).1 = _
  rw [h1]
  exact h2.symm

theorem stepB_root (c : GBranch (clSplicedGardenOfSlots hB hCL D).tree) :
    (stepB hB hCL D c).1.2 = [] ↔ c.1.2 = [] :=
  clSplicedBranchName_root_iff hB hCL D c

theorem stepB_parent (c : GBranch (clSplicedGardenOfSlots hB hCL D).tree) (hn : c.1.2 ≠ [])
    (ho : (stepB hB hCL D c).1.2 ≠ []) :
    stepB hB hCL D (GNode.parent c.toNode hn) = rep S a (GNode.parent (stepB hB hCL D c).toNode ho) := by
  apply eq_rep_of_contract hB.2.1 (stepB_mem hB hCL D _)
  have h1 := clSplicedBranchName_contract hB hCL D (GNode.parent c.toNode hn)
  have h2 := cl_branch_name_parent_contract hB hCL D c hn ho
  change contractVertex S (clSplicedBranchNameEquiv hB hCL D _).1 = _
  rw [h1]
  exact h2.symm

end WaveTurbulence.RedSplice
