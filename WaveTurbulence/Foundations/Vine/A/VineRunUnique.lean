/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitTransport
public import WaveTurbulence.Foundations.Molecule.VineNestedBlockRecognition
/-! Uniqueness of the left run of a block cut around a fixed ingredient.
Connectivity of the other run prevents a second cut crossing its boundary. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.RedSplice
variable {V D : Type*} [DecidableEq V] [Fintype D]
variable {N : Molecule V D} {S A L R L' R' : Finset V} {a b x y : V}

/-- A cut with connected runs determines the left atom set of every other cut. -/
theorem run_left_unique (H : SkelDecomp N S A L R a b x y)
    (K : SkelDecomp N S A L' R' a b x y) : L = L' := by
  classical
  have hLc : Vine.GroupConnected N L' := by
    rcases K.hL with ⟨he, _⟩ | ⟨_, hB, _⟩
    · subst L'; intro u hu; exact (Finset.notMem_empty u hu).elim
    · exact (LGSpine.groupConnected_of_block hB).2
  have hRc : Vine.GroupConnected N R' := by
    rcases K.hR with ⟨he, _⟩ | ⟨_, hB, _⟩
    · subst R'; intro u hu; exact (Finset.notMem_empty u hu).elim
    · exact (LGSpine.groupConnected_of_block hB).2
  rcases H.hL with ⟨hL, hxa⟩ | ⟨hxa, hLB, hi⟩
  · rcases K.hL with ⟨hL', _⟩ | ⟨hne, _⟩
    · exact hL.trans hL'.symm
    · exact (hne hxa).elim
  · obtain ⟨hL'B, hi'⟩ : N.IsBlock L' a x ∧ L' ∩ A = {x} := by
      rcases K.hL with ⟨_, h⟩ | ⟨_, hB, h⟩
      · exact (hxa h).elim
      · exact ⟨hB, h⟩
    have hxy : x ≠ y := H.hA.2.2.2.1
    have hyL : y ∉ L := by
      intro hy
      have hz := mem_inter.mpr ⟨hy, H.hA.2.2.1⟩
      rw [hi, mem_singleton] at hz
      exact hxy hz.symm
    have hsub : L ⊆ L' := by
      intro v hv
      have hvS : v ∈ S := by rw [H.hS]; exact mem_union_left _ (mem_union_left _ hv)
      rw [K.hS] at hvS
      rcases mem_union.mp hvS with hvS | hvR
      · rcases mem_union.mp hvS with hvL | hvA
        · exact hvL
        · have hz := mem_inter.mpr ⟨hv, hvA⟩
          rw [hi, mem_singleton] at hz
          exact hz ▸ hL'B.2.2.1
      · exfalso
        obtain ⟨hyR, _⟩ : y ∈ R' ∧ R' ≠ ∅ := by
          rcases K.hR with ⟨he, _⟩ | ⟨_, hB, _⟩
          · rw [he] at hvR; exact (Finset.notMem_empty v hvR).elim
          · exact ⟨hB.2.1, ne_empty_of_mem hB.2.1⟩
        have hd : ∀ z ∈ L, z ∈ R' → N.degIn L z = 4 := by
          intro z hz hzR
          have hza : z ≠ a := fun he =>
            (disjoint_left.mp K.hd (he ▸ hL'B.2.1)) hzR
          have hzx : z ≠ x := fun he =>
            (disjoint_left.mp K.hd (he ▸ hL'B.2.2.1)) hzR
          exact hLB.2.2.2.2.2.2.2.2.1 z hz hza hzx
        exact hyL ((Mole.induced_path_barrier N H.mol hLB.1 hd (hRc v hvR y hyR)).mp hv)
    exact Vine.nested_blocks_both_joints_eq N hLB hL'B hLc hsub hLB.2.1 hLB.2.2.1

/-- Reverse both the chain and its skipped ingredient. -/
theorem reverseCut (H : SkelDecomp N S A L R a b x y) : SkelDecomp N S A R L b a y x := by
  classical
  exact {
    mol := H.mol
    hS := H.hS.trans (by ext v; simp only [mem_union]; tauto)
    hSB := Mole.block_swap_joints N H.hSB
    hA := Mole.block_swap_joints N H.hA
    hL := H.hR.imp id (fun ⟨hne, hB, hi⟩ => ⟨hne, Mole.block_swap_joints N hB, hi⟩)
    hR := H.hL.imp id (fun ⟨hne, hB, hi⟩ => ⟨hne, Mole.block_swap_joints N hB, hi⟩)
    hd := H.hd.symm }

/-- Both runs of a cut are unique, including the empty-run cases. -/
theorem run_unique (H : SkelDecomp N S A L R a b x y)
    (K : SkelDecomp N S A L' R' a b x y) : L = L' ∧ R = R' :=
  ⟨run_left_unique H K, run_left_unique (reverseCut H) (reverseCut K)⟩

end WaveTurbulence.VineA
