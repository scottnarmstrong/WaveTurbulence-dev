/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.BlockParentTerminals
public import WaveTurbulence.Foundations.Molecule.RootCLIsolation
public import WaveTurbulence.Foundations.Molecule.ComponentSingletons
import Mathlib.Tactic

/-! # Zero-deficit components force actual isolated upper CL joints
TARGET `cnblock`, direct degree-budget proof. A zero-deficit parent path
cannot stop at an old root and therefore stops at a degree-four lower
CL joint, whose paired upper joint has ambient degree two.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w) (F : Finset (GardenBlockSegment G))

theorem zero_deficit_component_has_isolated_upper
    (hdis : Set.PairwiseDisjoint (F : Set (GardenBlockSegment G)) GardenBlockSegment.atoms)
    (hkind : ∀ B ∈ F, IsCNOrRootCL G B)
    {C : Finset (GBranch G.tree)} (hC : C ∈ Degen.componentSets (removeBlockFamily G F))
    (hzero : ∑ v ∈ C, (4-G.molecule.deg v) = 0) :
    ∃ B ∈ F, B.rightJoint ∈ C ∧ G.molecule.deg B.rightJoint = 4 ∧
      G.molecule.deg B.leftJoint = 2 ∧ B.leftJoint ∈ (removeBlockFamily G F).atoms ∧
      (removeBlockFamily G F).deg B.leftJoint = 0 := by
  have hfull : ∀ v ∈ C, G.molecule.deg v = 4 := by
    intro v hv
    have hw := Finset.single_le_sum (fun z (_hz : z ∈ C) => Nat.zero_le (4-G.molecule.deg z)) hv
    rw [hzero] at hw
    have hd := garden_molecule_deg_le_four G v
    omega
  obtain ⟨v,hv⟩ := componentSets_nonempty (removeBlockFamily G F) hC
  have hvM := componentSets_subset_atoms (removeBlockFamily G F) hC hv
  obtain ⟨z,hz,hvz,ht⟩ := residual_parent_terminal G F hkind v (mem_sdiff.mp hvM).2
  have hzC := componentSets_path_mem (removeBlockFamily G F) hC hv hvz
  have hz4 := hfull z hzC
  rcases ht with hr | ⟨B,hBF,he,hCL,hroot⟩
  · have hle := root_degree_le_three G z hr
    omega
  · have hbC : B.rightJoint ∈ C := he ▸ hzC
    have hb4 : G.molecule.deg B.rightJoint = 4 := he ▸ hz4
    have ha2 : G.molecule.deg B.leftJoint = 2 := by
      have hd := (block_joint_degrees G.molecule B.block).1
      have hl := degIn_le_deg G.molecule B.atoms B.leftJoint
      omega
    obtain ⟨haM,ha0⟩ := block_family_degree_two_joint_isolated G F hdis B hBF B.leftJoint (Or.inl rfl) ha2
    exact ⟨B,hBF,hbC,hb4,ha2,haM,ha0⟩

/-- Concrete charge data, constructed only after the zero-component theorem. -/
structure ZeroComponentChargeData (C : Finset (GBranch G.tree)) where
  block : GardenBlockSegment G
  block_mem : block ∈ F
  lower_mem : block.rightJoint ∈ C
  upper_degree : G.molecule.deg block.leftJoint = 2
  upper_survives : block.leftJoint ∈ (removeBlockFamily G F).atoms
  upper_isolated : (removeBlockFamily G F).deg block.leftJoint = 0

@[expose] noncomputable def zeroComponentChargeData
    (hdis : Set.PairwiseDisjoint (F : Set (GardenBlockSegment G)) GardenBlockSegment.atoms)
    (hkind : ∀ B ∈ F, IsCNOrRootCL G B)
    {C : Finset (GBranch G.tree)} (hC : C ∈ Degen.componentSets (removeBlockFamily G F))
    (hzero : ∑ v ∈ C, (4-G.molecule.deg v) = 0) : ZeroComponentChargeData G F C := by
  classical
  apply Classical.choice
  obtain ⟨B,hBF,hbC,_hb4,ha2,haM,ha0⟩ := zero_deficit_component_has_isolated_upper G F hdis hkind hC hzero
  exact ⟨⟨B,hBF,hbC,ha2,haM,ha0⟩⟩

end WaveTurbulence.Mole
