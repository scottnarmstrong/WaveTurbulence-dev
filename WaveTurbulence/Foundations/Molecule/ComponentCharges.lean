/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.ZeroDeficitComponents
import Mathlib.Tactic

/-! # Injecting zero-deficit components into positive isolated components
TARGET `cnblock`: disjoint blocks make the concrete charge injective.
-/

public section
namespace WaveTurbulence.Mole
open Finset TTree
variable {w : ℕ} (G : Garden w) (F : Finset (GardenBlockSegment G))

abbrev ZeroResidualComponent :=
  {C : Finset (GBranch G.tree) // C ∈ Degen.componentSets (removeBlockFamily G F) ∧
    (∑ v ∈ C, (4-G.molecule.deg v)) = 0}

abbrev PositiveResidualComponent :=
  {C : Finset (GBranch G.tree) // C ∈ Degen.componentSets (removeBlockFamily G F) ∧
    0 < ∑ v ∈ C, (4-G.molecule.deg v)}

variable (hdis : Set.PairwiseDisjoint (F : Set (GardenBlockSegment G)) GardenBlockSegment.atoms)
variable (hkind : ∀ B ∈ F, IsCNOrRootCL G B)

@[expose] noncomputable def zeroResidualCharge (C : ZeroResidualComponent G F) : PositiveResidualComponent G F := by
  let W := zeroComponentChargeData G F hdis hkind C.2.1 C.2.2
  refine ⟨Degen.componentSet (removeBlockFamily G F) W.block.leftJoint,⟨?_,?_⟩⟩
  · exact mem_image.mpr ⟨W.block.leftJoint,W.upper_survives,rfl⟩
  · rw [componentSet_eq_singleton_of_degree_zero (removeBlockFamily G F) W.upper_survives W.upper_isolated]
    simp only [sum_singleton,W.upper_degree]
    decide

theorem zeroResidualCharge_singleton (C : ZeroResidualComponent G F) :
    (zeroResidualCharge G F hdis hkind C).1 =
      {(zeroComponentChargeData G F hdis hkind C.2.1 C.2.2).block.leftJoint} := by
  let W := zeroComponentChargeData G F hdis hkind C.2.1 C.2.2
  change Degen.componentSet (removeBlockFamily G F) W.block.leftJoint = {W.block.leftJoint}
  exact componentSet_eq_singleton_of_degree_zero (removeBlockFamily G F) W.upper_survives W.upper_isolated

/-- Distinct zero components cannot charge the same isolated upper joint:
the corresponding blocks are disjoint, and their lower joints determine
their original zero components. -/
theorem zeroResidualCharge_injective : Function.Injective (zeroResidualCharge G F hdis hkind) := by
  intro C D he
  let WC := zeroComponentChargeData G F hdis hkind C.2.1 C.2.2
  let WD := zeroComponentChargeData G F hdis hkind D.2.1 D.2.2
  have hc : (zeroResidualCharge G F hdis hkind C).1 = {WC.block.leftJoint} :=
    zeroResidualCharge_singleton G F hdis hkind C
  have hd : (zeroResidualCharge G F hdis hkind D).1 = {WD.block.leftJoint} :=
    zeroResidualCharge_singleton G F hdis hkind D
  have hsingle : ({WC.block.leftJoint} : Finset (GBranch G.tree)) = {WD.block.leftJoint} :=
    hc.symm.trans ((congrArg Subtype.val he).trans hd)
  have hv : WC.block.leftJoint = WD.block.leftJoint := Finset.singleton_injective hsingle
  have hB : WC.block = WD.block := by
    by_contra hn
    have hboth : WC.block.leftJoint ∈ WD.block.atoms := hv.symm ▸ WD.block.block.2.1
    exact Finset.disjoint_left.mp (hdis WC.block_mem WD.block_mem hn) WC.block.block.2.1 hboth
  have hlowerD : WC.block.rightJoint ∈ D.1 := hB.symm ▸ WD.lower_mem
  apply Subtype.ext
  by_contra hn
  exact Finset.disjoint_left.mp
    (componentSets_pairwise_disjoint (removeBlockFamily G F) C.2.1 D.2.1 hn) WC.lower_mem hlowerD

end WaveTurbulence.Mole
