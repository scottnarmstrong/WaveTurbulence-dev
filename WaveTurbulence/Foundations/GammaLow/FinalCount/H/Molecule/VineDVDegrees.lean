/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineDVDegrees
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
public import WaveTurbulence.Foundations.Molecule.MoleculeConnectedBlocks
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineDVDegrees`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Actual degree profile of a double vine -/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- At a joint of a block there is no loop: the joint has internal degree `2` and the group is connected. -/
theorem block_joint_noLoop {M : Molecule V D} {S : Finset V} {a b : V} (hB : M.IsBlock S a b) :
    ∀ x, M.atom x = a → M.atom (M.mate x) ≠ a := fun _ hx =>
  Mole.connected_degree_two_no_loop M (Molecpl.connected_to_induced M ⟨a, hB.2.1⟩ hB.2.2.2.2.2.2.2.2.2) hB.2.1
    hB.2.2.1 hB.2.2.2.1.symm (Mole.block_joint_degrees M hB).1 hx

/-- TARGET vinechainlem: a DV has degree-three joints and degree-four
interior atoms. The shared type-V joint bond is counted exactly once. -/
theorem isDV_degree_profile (M : Molecule V D) (hM : M.IsMolecule)
    {U : Finset V} {a b : V} (hU : Src.IsDV Src.γL M U a b) :
    M.degIn U a=3 ∧ M.degIn U b=3 ∧
      ∀ v ∈ U,v ≠ a → v ≠ b → M.degIn U v=4 := by
  obtain ⟨hσ, S,T,hS,hT,hi,rfl⟩ := hU
  have hs := Mole.block_joint_degrees M (Src.isBlock_of_isSomeVine hS)
  have ht := Mole.block_joint_degrees M (Src.isBlock_of_isSomeVine hT)
  -- DV′: `σ(a, b) = 1`, and a joint carries no loop, so the joint-pair degrees are `1`
  have hBS := Src.isBlock_of_isSomeVine hS
  have hp : M.degIn {a,b} a=1 ∧ M.degIn {a,b} b=1 := by
    refine ⟨?_, ?_⟩
    · rw [Mole.degIn_pair_eq_bondsBetween M hBS.2.2.2.1 (block_joint_noLoop hBS)]; exact hσ
    · rw [Finset.pair_comm, Mole.degIn_pair_eq_bondsBetween M hBS.2.2.2.1.symm
        (block_joint_noLoop (Src.isBlock_swap' hBS)), Mole.bondsBetween_symm]; exact hσ
  have hda := degIn_union_inter M S T a (Src.isBlock_of_isSomeVine hS).2.1 (Src.isBlock_of_isSomeVine hT).2.1
  have hdb := degIn_union_inter M S T b (Src.isBlock_of_isSomeVine hS).2.2.1 (Src.isBlock_of_isSomeVine hT).2.2.1
  rw [hi,hp.1,hs.1,ht.1] at hda
  rw [hi,hp.2,hs.2,ht.2] at hdb
  refine ⟨by omega,by omega,?_⟩
  intro v hv hva hvb
  have hvm : v ∈ M.atoms := (union_subset (Src.isBlock_of_isSomeVine hS).1 (Src.isBlock_of_isSomeVine hT).1) hv
  have hbound := (Mole.degIn_le_deg M (S ∪ T) v).trans (Mole.deg_le_four M hM hvm)
  rcases mem_union.mp hv with hv | hv
  · have hd := (Src.isBlock_of_isSomeVine hS).2.2.2.2.2.2.2.2.1 v hv hva hvb
    have hle := degIn_mono M (show S ⊆ S ∪ T from subset_union_left) v
    omega
  · have hd := (Src.isBlock_of_isSomeVine hT).2.2.2.2.2.2.2.2.1 v hv hva hvb
    have hle := degIn_mono M (show T ⊆ S ∪ T from subset_union_right) v
    omega

end WaveTurbulence.GammaLow.FinalCount.H
