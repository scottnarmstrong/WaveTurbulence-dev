/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.Molecule.VineHyperVertexConnected
public import WaveTurbulence.Foundations.Molecule.VineLowDegreeJoints
public import WaveTurbulence.Foundations.Molecule.VineNestedDegreeClosure
public import WaveTurbulence.Foundations.Molecule.VineLikeConnected
public import WaveTurbulence.Foundations.Molecule.MoleculeHyperBlocks
import Mathlib.Tactic

/-! # Inner objects containing both outer hyper-object joints -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The nonjoint region of a hyper-vine-like object is connected: deleting
the designated closing bond does not affect that region, and the adjoint
chain has a connected nonjoint interior. -/
theorem hyperLike_interior_connected (M : Molecule V D) {U : Finset V} {a b : V}
    (hU : IsHV M U a b ∨ IsHVC M U a b) : GroupConnected M (U \ {a,b}) := by
  obtain ⟨e,_he,_hB,n,hchain⟩ := hyperLike_iff_adjoint_VC.mp hU
  intro u hu v hv
  exact eraseBond_induced_path M e _ (chain_interior_connected hchain u hu v hv)

/-- TARGET subsetvc, ordinary both-joints case: a block contained in an
HV/HVC and containing both outer joints consists of just those two atoms.
Full-degree closure in the connected nonjoint region rules out every other atom. -/
theorem block_in_hyperLike_both_joints_atoms (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V} (hU : IsHV M U a b ∨ IsHVC M U a b)
    (hA : M.IsBlock A x y) (hAU : A ⊆ U) (ha : a ∈ A) (hb : b ∈ A) : A={a,b} := by
  obtain ⟨e,he,hB,n,hchain⟩ := hyperLike_iff_adjoint_VC.mp hU
  have hH : Mole.IsHyperBlock M U a b := ⟨e,he,hB⟩
  have hd := Mole.hyperBlock_degrees M hH
  have hj := joints_eq_of_two_low_degrees M hAU ha hb hB.2.2.2.1 hA.2.2.2.1
    hd.1.le hd.2.1.le hA.2.2.2.2.2.2.2.2.1
  have hda : M.degIn A a=2 := by
    have ham : a ∈ ({x,y} : Finset V) := hj.symm ▸ mem_insert_self _ _
    rcases mem_insert.mp ham with hax | hay
    · exact hax.symm ▸ (Mole.block_joint_degrees M hA).1
    · exact (mem_singleton.mp hay).symm ▸ (Mole.block_joint_degrees M hA).2
  apply Subset.antisymm
  · intro u huA
    by_contra hun
    have huI : u ∈ U \ {a,b} := mem_sdiff.mpr ⟨hAU huA,hun⟩
    have hclosed : ∀ v ∈ A,v ∈ U \ {a,b} → M.degIn A v=4 := by
      intro v hvA hvI
      have hvj : v ∉ ({x,y} : Finset V) := hj.symm ▸ (mem_sdiff.mp hvI).2
      have hne : v ≠ x ∧ v ≠ y := by simpa only [mem_insert,mem_singleton,not_or] using hvj
      exact hA.2.2.2.2.2.2.2.2.1 v hvA hne.1 hne.2
    have hUA : U ⊆ A := by
      intro v hvU
      by_cases hvj : v ∈ ({a,b} : Finset V)
      · rcases mem_insert.mp hvj with rfl | hvj
        · exact ha
        · exact mem_singleton.mp hvj ▸ hb
      · have hp := hyperLike_interior_connected M hU u huI v (mem_sdiff.mpr ⟨hvU,hvj⟩)
        exact (Mole.induced_path_barrier M hM hA.1 hclosed hp).mp huA
    have heq := Subset.antisymm hAU hUA
    rw [heq,hd.1] at hda
    omega
  · intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact ha
    · exact mem_singleton.mp hv ▸ hb

/-- TARGET subsetvc, hyper both-joints case: a contained hyper-block
which contains both outer joints is the entire outer hyper-vine-like group.
Equality of all actual nested degrees makes it closed in the connected group. -/
theorem hyperBlock_in_hyperLike_both_joints_eq (M : Molecule V D)
    {A U : Finset V} {a b x y : V} (hU : IsHV M U a b ∨ IsHVC M U a b)
    (hA : Mole.IsHyperBlock M A x y) (hAU : A ⊆ U) (ha : a ∈ A) (hb : b ∈ A) : A=U := by
  obtain ⟨e,he,hB,_n,_hchain⟩ := hyperLike_iff_adjoint_VC.mp hU
  obtain ⟨f,hf,hAB⟩ := hA
  have hdU := Mole.hyperBlock_degrees M (show Mole.IsHyperBlock M U a b from ⟨e,he,hB⟩)
  have hdA := Mole.hyperBlock_degrees M (show Mole.IsHyperBlock M A x y from ⟨f,hf,hAB⟩)
  have hj := joints_eq_of_two_low_degrees M hAU ha hb hB.2.2.2.1 hAB.2.2.2.1
    hdU.1.le hdU.2.1.le hdA.2.2
  have hconn : GroupConnected M U := by
    rcases hU with h | h
    · exact isHV_connected h
    · exact isHVC_connected h
  apply nested_degree_eq_of_connected M hAU ⟨a,ha⟩ hconn
  intro v hvA
  by_cases hvx : v=x
  · have hvm : v ∈ ({a,b} : Finset V) := hj ▸ (hvx.symm ▸ mem_insert_self x ({y} : Finset V))
    rw [show M.degIn A v=3 from hvx.symm ▸ hdA.1]
    rcases mem_insert.mp hvm with hva | hvb
    · exact (hva ▸ hdU.1).symm
    · exact (mem_singleton.mp hvb ▸ hdU.2.1).symm
  · by_cases hvy : v=y
    · have hvm : v ∈ ({a,b} : Finset V) := hj ▸ (hvy.symm ▸ mem_insert_of_mem (mem_singleton_self y))
      rw [show M.degIn A v=3 from hvy.symm ▸ hdA.2.1]
      rcases mem_insert.mp hvm with hva | hvb
      · exact (hva ▸ hdU.1).symm
      · exact (mem_singleton.mp hvb ▸ hdU.2.1).symm
    · have hvj : v ∉ ({a,b} : Finset V) := by rw [← hj]; simp only [mem_insert,mem_singleton]; exact not_or.mpr ⟨hvx,hvy⟩
      have hvab : v ≠ a ∧ v ≠ b := by simpa only [mem_insert,mem_singleton,not_or] using hvj
      exact (hdA.2.2 v hvA hvx hvy).trans (hdU.2.2 v (hAU hvA) hvab.1 hvab.2).symm
end WaveTurbulence.Vine
