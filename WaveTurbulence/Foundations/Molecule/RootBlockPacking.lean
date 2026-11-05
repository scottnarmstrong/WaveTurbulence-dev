/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.GardenDeficitBound
public import WaveTurbulence.Foundations.Molecule.BlockChains
import Mathlib.Tactic

/-! # At most R disjoint root blocks in a plain garden of width 2R
TARGET `cnblock`, first paragraph. This proves the degree-counting step
also for reducible and zero-order gardens.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {R : ℕ} (G : Garden (2*R))

/-- Every root block consumes at least two units of the ambient deficit. -/
theorem root_block_joint_deficit (A : GardenBlockSegment G)
    (hr : G.molecule.deg A.leftJoint + G.molecule.deg A.rightJoint ≤ 6) :
    2 ≤ (4-G.molecule.deg A.leftJoint) + (4-G.molecule.deg A.rightJoint) := by
  have h1 := garden_molecule_deg_le_four G A.leftJoint
  have h2 := garden_molecule_deg_le_four G A.rightJoint
  omega

/-- TARGET `cnblock`: any disjoint family of root blocks has cardinality at most R.
Only the defining degree condition is used, so the conclusion also holds
for connected blocks before restricting the family to CL blocks. -/
theorem root_block_family_card_le {ι : Type*} [DecidableEq ι]
    (hP : G.IsPlain) (F : Finset ι) (B : ι → GardenBlockSegment G)
    (hdis : Set.PairwiseDisjoint (F : Set ι) (fun i => (B i).atoms))
    (hr : ∀ i ∈ F, G.molecule.deg (B i).leftJoint + G.molecule.deg (B i).rightJoint ≤ 6) :
    F.card ≤ R := by
  classical
  let P : ι → Finset (GBranch G.tree) := fun i => {(B i).leftJoint,(B i).rightJoint}
  have hsub : ∀ i, P i ⊆ (B i).atoms := by
    intro i v hv
    simp only [P,mem_insert,mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact (B i).block.2.1
    · exact (B i).block.2.2.1
  have hpd : Set.PairwiseDisjoint (F : Set ι) P := by
    intro i hi j hj hn
    exact (hdis hi hj hn).mono (hsub i) (hsub j)
  have hlow : 2*F.card ≤ ∑ i ∈ F, ∑ v ∈ P i, (4-G.molecule.deg v) := by
    calc
      _ = ∑ _i ∈ F, 2 := by simp [Nat.mul_comm]
      _ ≤ _ := by
        apply sum_le_sum
        intro i hi
        have hn := (B i).block.2.2.2.1
        have he : ∑ v ∈ P i, (4-G.molecule.deg v) =
            (4-G.molecule.deg (B i).leftJoint) + (4-G.molecule.deg (B i).rightJoint) := by
          simp only [P,Finset.sum_pair hn]
        rw [he]
        exact root_block_joint_deficit G (B i) (hr i hi)
  have hu : F.biUnion P ⊆ G.molecule.atoms := by
    intro v hv
    obtain ⟨i,hi,hvi⟩ := mem_biUnion.mp hv
    exact (B i).block.1 (hsub i hvi)
  have hhigh : (∑ i ∈ F, ∑ v ∈ P i, (4-G.molecule.deg v)) ≤ 2*R := by
    rw [← Finset.sum_biUnion hpd]
    exact (Finset.sum_le_sum_of_subset hu).trans (plain_garden_degree_deficit_le_width G hP)
  omega

end WaveTurbulence.Mole
