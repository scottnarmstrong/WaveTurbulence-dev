/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.MoleculeBlockBarriers
public import WaveTurbulence.Foundations.Molecule.VineDegreeUnionIntersection
/-! The no-saturated-component axiom excludes three disjoint type-V branches at the same joints. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

private theorem source_degIn_mono {V D : Type*} [DecidableEq V] [Fintype D]
    (M : Molecule V D) {A U : Finset V} (h : A ⊆ U) (v : V) :
    M.degIn A v ≤ M.degIn U v := by
  classical
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hx, hxA, hxA'⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hx, h hxA, h hxA'⟩

/-- The geometric exclusion underlying uniqueness of a double-vine partner. All
assumptions are actual half-edge degree and block data. -/
theorem no_three_joint_blocks {V D : Type*} [DecidableEq V] [Fintype D]
    (M : Molecule V D) (hM : M.IsMolecule) {A B C : Finset V} {a b : V}
    (hA : M.IsBlock A a b) (hB : M.IsBlock B a b) (hC : M.IsBlock C a b)
    (hAB : A ∩ B = {a,b}) (hAC : A ∩ C = {a,b}) (hBC : B ∩ C = {a,b})
    (hpair : ∀ v ∈ ({a,b} : Finset V), M.degIn {a,b} v = 1) : False := by
  classical
  let U := A ∪ B ∪ C
  have hAU : A ⊆ U := fun _ h => mem_union_left _ (mem_union_left _ h)
  have hBU : B ⊆ U := fun _ h => mem_union_left _ (mem_union_right _ h)
  have hCU : C ⊆ U := fun _ h => mem_union_right _ h
  have hsub : U ⊆ M.atoms := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · rcases mem_union.mp hv with hv | hv
      · exact hA.1 hv
      · exact hB.1 hv
    · exact hC.1 hv
  have hInt : (A ∪ B) ∩ C = {a,b} := by
    rw [union_inter_distrib_right, hAC, hBC, union_self]
  have hjoint (v : V) (hv : v ∈ ({a,b} : Finset V)) : M.degIn U v = 4 := by
    have hda : M.degIn A v = 2 := by
      rcases mem_insert.mp hv with rfl | hv
      · exact (Mole.block_joint_degrees M hA).1
      · exact (mem_singleton.mp hv).symm ▸ (Mole.block_joint_degrees M hA).2
    have hdb : M.degIn B v = 2 := by
      rcases mem_insert.mp hv with rfl | hv
      · exact (Mole.block_joint_degrees M hB).1
      · exact (mem_singleton.mp hv).symm ▸ (Mole.block_joint_degrees M hB).2
    have hdc : M.degIn C v = 2 := by
      rcases mem_insert.mp hv with rfl | hv
      · exact (Mole.block_joint_degrees M hC).1
      · exact (mem_singleton.mp hv).symm ▸ (Mole.block_joint_degrees M hC).2
    have hvA : v ∈ A := by rw [← hAB] at hv; exact (mem_inter.mp hv).1
    have hvB : v ∈ B := by rw [← hAB] at hv; exact (mem_inter.mp hv).2
    have hvC : v ∈ C := by rw [← hAC] at hv; exact (mem_inter.mp hv).2
    have h1 := Vine.degIn_union_inter M A B v hvA hvB
    have h2 := Vine.degIn_union_inter M (A ∪ B) C v (mem_union_left _ hvA) hvC
    rw [hAB, hpair v hv, hda, hdb] at h1
    rw [hInt, hpair v hv, hdc] at h2
    dsimp only [U]
    omega
  apply Mole.no_saturated_group M hM hsub ⟨a, hAU hA.2.1⟩
  intro v hv
  by_cases hj : v ∈ ({a,b} : Finset V)
  · exact hjoint v hj
  have hj' : v ≠ a ∧ v ≠ b := by simpa only [mem_insert, mem_singleton, not_or] using hj
  have hva := hj'.1
  have hvb := hj'.2
  have hlow : 4 ≤ M.degIn U v := by
    rcases mem_union.mp hv with hv | hv
    · rcases mem_union.mp hv with hv | hv
      · have hd := hA.2.2.2.2.2.2.2.2.1 v hv hva hvb
        rw [← hd]
        exact source_degIn_mono M hAU v
      · have hd := hB.2.2.2.2.2.2.2.2.1 v hv hva hvb
        rw [← hd]
        exact source_degIn_mono M hBU v
    · have hd := hC.2.2.2.2.2.2.2.2.1 v hv hva hvb
      rw [← hd]
      exact source_degIn_mono M hCU v
  exact Nat.le_antisymm ((Mole.degIn_le_deg M U v).trans (Mole.deg_le_four M hM (hsub hv))) hlow

end WaveTurbulence.LGSpine
