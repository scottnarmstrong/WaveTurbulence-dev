/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceDarts
public import WaveTurbulence.Foundations.Spine.SourceJointPairDichotomy
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): opposite dart pairs at the joints of blocks

* `block_pair`: at a joint of a block, an out-dart and an in-dart of the block that are not mates.
* `ext_pair_deg4`: at a joint of degree `4` of a block, an out-dart and an in-dart that are NOT in the block.
* `ext_pair_run`: at the joint `x` of a vine `A` shared with a run `L0` with `L0 ∩ A = {x}`, the out- and in-dart of
  `A` at `x` are not in `L0`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- External dart pair at the joint `j` of the group `U`: an out-dart and an in-dart at `j`, neither in `U`. -/
@[expose] def HasExtPair (M : Molecule V D) (U : Finset V) (j : V) : Prop :=
  ∃ d1 d2 : D, M.atom d1 = j ∧ M.atom d2 = j ∧ ¬ M.InGroup U d1 ∧ ¬ M.InGroup U d2 ∧
    M.out d1 = true ∧ M.out d2 = false

theorem block_pair {S : Finset V} {j1 j2 : V} (hB : M.IsBlock S j1 j2) :
    ∃ x y : D, M.atom x = j1 ∧ M.atom y = j1 ∧ M.InGroup S x ∧ M.InGroup S y ∧ M.out x = true ∧
      M.out y = false ∧ y ≠ M.mate x := by
  classical
  have ho : ((M.dartsAt j1).filter fun x => M.InGroup S x ∧ M.out x = true).card = 1 := hB.2.2.2.2.1
  have hi : ((M.dartsAt j1).filter fun x => M.InGroup S x ∧ M.out x = false).card = 1 := hB.2.2.2.2.2.1
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < ((M.dartsAt j1).filter fun x => M.InGroup S x ∧ M.out x = true).card)
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < ((M.dartsAt j1).filter fun x => M.InGroup S x ∧ M.out x = false).card)
  rw [Finset.mem_filter, Mole.mem_dartsAt] at hx hy
  refine ⟨x, y, hx.1, hy.1, hx.2.1, hy.2.1, hx.2.2, hy.2.2, ?_⟩
  intro hxy
  -- a loop at the joint contradicts connectivity
  have hc : Mole.GroupConnected M S := WaveTurbulence.LGSpine.groupConnected_of_block hB
  have hdeg := (block_joint_degrees M hB).1
  exact connected_degree_two_no_loop M hc hB.2.1 hB.2.2.1 (Ne.symm hB.2.2.2.1) hdeg hx.1
    (by rw [← hxy]; exact hy.1)

theorem ext_pair_deg4 (hM : M.IsMolecule) {S : Finset V} {j1 j2 : V} (hB : M.IsBlock S j1 j2)
    (h4 : M.deg j1 = 4) : HasExtPair M S j1 := by
  classical
  have hat : j1 ∈ M.atoms := hB.1 hB.2.1
  have hsum := outdeg_add_indeg M j1
  have hin := hM.1 j1 hat
  have ho : ((M.dartsAt j1).filter fun x => M.InGroup S x ∧ M.out x = true).card = 1 := hB.2.2.2.2.1
  have hi : ((M.dartsAt j1).filter fun x => M.InGroup S x ∧ M.out x = false).card = 1 := hB.2.2.2.2.2.1
  have hod : M.outdeg j1 = 2 := by omega
  have hid : M.indeg j1 = 2 := by omega
  have h1 : ((M.dartsAt j1).filter fun x => M.InGroup S x ∧ M.out x = true) ⊂
      ((M.dartsAt j1).filter fun x => M.out x = true) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro z hz; rw [Finset.mem_filter] at hz ⊢; exact ⟨hz.1, hz.2.2⟩
    · intro h; have := congrArg Finset.card h; unfold Molecule.outdeg at hod; omega
  have h2 : ((M.dartsAt j1).filter fun x => M.InGroup S x ∧ M.out x = false) ⊂
      ((M.dartsAt j1).filter fun x => M.out x = false) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro z hz; rw [Finset.mem_filter] at hz ⊢; exact ⟨hz.1, hz.2.2⟩
    · intro h; have := congrArg Finset.card h; unfold Molecule.indeg at hid; omega
  obtain ⟨d1, hd1, hd1n⟩ := Finset.exists_of_ssubset h1
  obtain ⟨d2, hd2, hd2n⟩ := Finset.exists_of_ssubset h2
  rw [Finset.mem_filter, Mole.mem_dartsAt] at hd1 hd2
  refine ⟨d1, d2, hd1.1, hd2.1, ?_, ?_, hd1.2, hd2.2⟩
  · intro hg
    apply hd1n
    rw [Finset.mem_filter]
    exact ⟨(Mole.mem_dartsAt M j1 d1).mpr hd1.1, hg, hd1.2⟩
  · intro hg
    apply hd2n
    rw [Finset.mem_filter]
    exact ⟨(Mole.mem_dartsAt M j1 d2).mpr hd2.1, hg, hd2.2⟩


section run
variable {D' : Type*} [Fintype D'] [DecidableEq D'] {N : Molecule V D'}

/-- The out- and in-dart of a block `A` at its joint `j` do not lead into a run `L0` meeting `A` only in `j`. -/
theorem ext_pair_run {A L0 : Finset V} {j j' : V} (hAB : N.IsBlock A j j') (hL : L0 ∩ A = {j}) :
    ∃ x y : D', N.atom x = j ∧ N.atom y = j ∧ N.out x = true ∧ N.out y = false ∧
      N.atom (N.mate x) ∈ A ∧ N.atom (N.mate y) ∈ A ∧
      N.atom (N.mate x) ∉ L0 ∧ N.atom (N.mate y) ∉ L0 := by
  obtain ⟨x, y, hx, hy, hxA, hyA, hxo, hyo, _⟩ := block_pair hAB
  have hc : Mole.GroupConnected N A := WaveTurbulence.LGSpine.groupConnected_of_block hAB
  have hdeg := (block_joint_degrees N hAB).1
  have hnl : ∀ z : D', N.atom z = j → N.InGroup A z → N.atom (N.mate z) ∉ L0 := by
    intro z hz hzA hzL
    have hmem : N.atom (N.mate z) ∈ L0 ∩ A := mem_inter.mpr ⟨hzL, hzA.2⟩
    rw [hL, mem_singleton] at hmem
    exact connected_degree_two_no_loop N hc hAB.2.1 hAB.2.2.1 (Ne.symm hAB.2.2.2.1) hdeg hz hmem
  exact ⟨x, y, hx, hy, hxo, hyo, hxA.2, hyA.2, hnl x hx hxA, hnl y hy hyA⟩

/-- Transfer to the molecule of an adjoint: external pair at the joint of the run. -/
theorem hasExt_of_run_erase {A L0 : Finset V} {j j' : V} (e : D)
    (hAB : (eraseBond M e).IsBlock A j j') (hL : L0 ∩ A = {j}) : HasExtPair M L0 j := by
  obtain ⟨x, y, hx, hy, hxo, hyo, _, _, hxn, hyn⟩ := ext_pair_run hAB hL
  refine ⟨x.1, y.1, hx, hy, ?_, ?_, hxo, hyo⟩
  · intro hg; exact hxn hg.2
  · intro hg; exact hyn hg.2

theorem hasExt_of_run {A L0 : Finset V} {j j' : V}
    (hAB : M.IsBlock A j j') (hL : L0 ∩ A = {j}) : HasExtPair M L0 j := by
  obtain ⟨x, y, hx, hy, hxo, hyo, _, _, hxn, hyn⟩ := ext_pair_run hAB hL
  refine ⟨x, y, hx, hy, ?_, ?_, hxo, hyo⟩
  · intro hg; exact hxn hg.2
  · intro hg; exact hyn hg.2

end run

end WaveTurbulence.RedSplice
