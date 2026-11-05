/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.ComponentCharges
public import WaveTurbulence.Foundations.Molecule.ComponentChargeLedger
public import WaveTurbulence.Foundations.Molecule.GardenDeficitBound
import Mathlib.Tactic

/-! # TARGET Proposition cnblock
The proof uses the ambient deficit budget and an injective charge from
zero-deficit components to isolated positive-deficit components. This
replaces the source's generalized-forest and root-block case enumeration.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset

/-- TARGET `cnblock` (L1367–1376). Remove any disjoint collection of CN
and root CL blocks, deleting their nonjoint atoms and all internal bonds.
The literal resulting molecule has at most 2R components; at equality
there is an actual isolated atom. `1 ≤ R` excludes the empty width-zero
garden and covers the packet's general-garden regime `R ≥ 2`. -/
theorem cnblock_component_bound {R : ℕ} (G : Garden (2*R)) (hP : G.IsPlain) (hR : 1 ≤ R)
    (F : Finset (GardenBlockSegment G))
    (hdis : Set.PairwiseDisjoint (F : Set (GardenBlockSegment G)) GardenBlockSegment.atoms)
    (hkind : ∀ B ∈ F, IsCNOrRootCL G B) :
    (removeBlockFamily G F).numComponents ≤ 2*R ∧
      ((removeBlockFamily G F).numComponents = 2*R →
        ∃ v ∈ (removeBlockFamily G F).atoms, (removeBlockFamily G F).deg v = 0) := by
  classical
  let M := removeBlockFamily G F
  let comps := Degen.componentSets M
  let weight : Finset (GBranch G.tree) → ℕ := fun C => ∑ v ∈ C, (4-G.molecule.deg v)
  have heven : ∀ C ∈ comps, Even (weight C) := fun C hC => even_residual_component_deficit G F hdis hC
  have hu : comps.biUnion (fun C => C) ⊆ G.molecule.atoms := by
    intro v hv
    obtain ⟨C,hC,hvC⟩ := mem_biUnion.mp hv
    have hvM := componentSets_subset_atoms M hC hvC
    exact (mem_sdiff.mp hvM).1
  have hbudget : ∑ C ∈ comps, weight C ≤ 2*R := by
    dsimp only [weight]
    rw [← Finset.sum_biUnion (componentSets_pairwise_disjoint M)]
    exact (sum_le_sum_of_subset hu).trans (plain_garden_degree_deficit_le_width G hP)
  have hledger := even_weight_charge_bound comps weight R hR heven hbudget
    (zeroResidualCharge G F hdis hkind) (zeroResidualCharge_injective G F hdis hkind)
  have hnum := Degen.numComponents_eq_card_componentSets M
  refine ⟨hnum.trans_le hledger.1,?_⟩
  intro heq
  obtain ⟨C,hC,hzero⟩ := hledger.2 (hnum.symm.trans heq)
  obtain ⟨B,_hB,_hbC,_hb4,_ha2,haM,ha0⟩ :=
    zero_deficit_component_has_isolated_upper G F hdis hkind hC hzero
  exact ⟨B.leftJoint,haM,ha0⟩

end WaveTurbulence.Mole
