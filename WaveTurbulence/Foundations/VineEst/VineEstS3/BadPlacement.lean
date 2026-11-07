/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.VineTwistPlacements
public import WaveTurbulence.Foundations.Molecule.CoreVine
public import WaveTurbulence.Foundations.Molecule.RegionIncidences

/-! # BadClause, part D1: a core vine has an internal selected placement

`core_placement_internal`: for a core CL vine `(S, a, b)` there is a `CorePlacement P` with `IsPlacementAt G S b P`
whose retained leaf is an internal leaf of `S` (LFTwist `corePlacement_at_vine` plus the internality of the retained
bond, which the proofs of `typeI_placementAt`/`typeII_placementAt` provide).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.Twist TTree
variable {w : ℕ} (G : Garden w)

theorem placement_internal_of_leaf_pair {S : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b) (hc : c ∈ S)
    {l : GLeaf G.tree} {i j : Fin 3} (hm : G.mark l = none)
    (hl : l.toNode = b.child i) (hr : (G.pair l).toNode = c.child j)
    (hout : ¬ b.toNode.IsDesc (G.pair l).toNode) :
    ∃ P : CorePlacement G, IsPlacementAt G S b P ∧ Mole.IsInternalLeaf G S P.retained := by
  have hn : l.1.2 ≠ [] := by
    change l.toNode.1.2 ≠ []
    rw [hl]
    exact Mole.child_nonroot G b i
  have hp : (G.pair l).1.2 ≠ [] := by
    change (G.pair l).toNode.1.2 ≠ []
    rw [hr]
    exact Mole.child_nonroot G c j
  refine ⟨⟨b, l, hCL.2.choose, hp, i, hm, hl, Molecpl.lower_leaf_outer G hB hCL hc hm hl hr, hout⟩,
    ⟨rfl, retained_slot_of_leaf_pair G hB hCL hc hm hl hr⟩, hm, hn, hp, ?_⟩
  let x : GardenDart G := .inr ⟨l, hm, hn, hp⟩
  have ha : G.molecule.atom x = b := parent_eq_of_child hn hl
  have hb : G.molecule.atom (G.molecule.mate x) = c := parent_eq_of_child hp hr
  change G.molecule.atom x ∈ S ∧ G.molecule.atom (G.molecule.mate x) ∈ S
  rw [ha, hb]
  exact ⟨hB.2.2.1, hc⟩

theorem core_placement_internal {X : VineType} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (h : IsCoreCLVine G X S a b) :
    ∃ P : CorePlacement G, IsPlacementAt G S b P ∧ Mole.IsInternalLeaf G S P.retained := by
  obtain ⟨hV, hCL, hcore⟩ := h
  rcases hcore with rfl | ⟨rfl, hcore⟩
  · obtain ⟨l, i, j, hm, hl, hr, _⟩ := Molecpl.typeI_leaf_pair G hV hCL
    refine placement_internal_of_leaf_pair G hV.1 hCL hV.1.2.1 hm hl hr ?_
    intro hd
    have hba := branch_desc_leaf_parent G hr hd
    have hlen := hba.2.length_le
    have hab := Mole.cl_parent_strict_descendant G hV.1 hCL
    dsimp [GBranch.toNode] at hlen
    omega
  · obtain ⟨R, hn, hp, hcases⟩ := Molecpl.garden_typeII_local_cases G hV hCL
    have hLP : Molecpl.LowerLP G R := by
      rcases hcases with ⟨_hall, hlp⟩ | ⟨_hparent, hlp, _hpc⟩ | ⟨_hparent, hlp, _hpc⟩ | ⟨hparent, hall⟩
      · exact hlp
      · exact hlp
      · exact hlp
      · obtain ⟨hqn, hqp⟩ := hparent
        obtain ⟨i, hi, hio, _⟩ := Molecpl.lower_child_retained G hV.1 hCL R.right_mem hqn hqp
        have hd : Molecpl.DoubleLeafPairAt G R.left R.right :=
          Molecpl.double_leaf_pair_positions G (Molecpl.FourIncidences.doublePair R.left_row) hall
        have ha := Mole.block_one_root_descendants G hV.1 hCL.1 hCL.2 R.left_mem
        exact (hcore ⟨R.left, R.left_mem, R.right, R.right_mem, ⟨hn, hp⟩, ⟨hqn, hqp⟩, hd, ⟨i, hi, hio⟩, ha⟩).elim
    obtain ⟨l, i, j, hm, hl, hr, _hi, _hs⟩ := Molecpl.lower_LP_retained G hV.1 hCL R hLP
    exact placement_internal_of_leaf_pair G hV.1 hCL R.right_mem hm hl hr
      (child_leaf_outside_of_terminal G R.right_mem R.right_ne_lower
        (Molecpl.lower_LP_terminal G hV.1 hCL R hLP) hr)

end WaveTurbulence.VineEstS3
