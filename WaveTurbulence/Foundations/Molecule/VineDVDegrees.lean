/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineJointPairDegrees
public import WaveTurbulence.Foundations.Molecule.VineDegreeUnionIntersection
public import WaveTurbulence.Foundations.Molecule.VineJointFlows
public import WaveTurbulence.Foundations.Molecule.VineObjects
import Mathlib.Tactic

/-! # Actual degree profile of a double vine -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- TARGET vinechainlem: a DV has degree-three joints and degree-four
interior atoms. The shared type-V joint bond is counted exactly once. -/
theorem isDV_degree_profile (M : Molecule V D) (hM : M.IsMolecule)
    {U : Finset V} {a b : V} (hU : IsDV M U a b) :
    M.degIn U a=3 ∧ M.degIn U b=3 ∧
      ∀ v ∈ U,v ≠ a → v ≠ b → M.degIn U v=4 := by
  obtain ⟨S,T,hS,hT,hi,rfl⟩ := hU
  have hs := Mole.block_joint_degrees M hS.1
  have ht := Mole.block_joint_degrees M hT.1
  have hp := isVine_joint_pair_degrees hS
  change M.degIn {a,b} a=1 ∧ M.degIn {a,b} b=1 at hp
  have hda := degIn_union_inter M S T a hS.1.2.1 hT.1.2.1
  have hdb := degIn_union_inter M S T b hS.1.2.2.1 hT.1.2.2.1
  rw [hi,hp.1,hs.1,ht.1] at hda
  rw [hi,hp.2,hs.2,ht.2] at hdb
  refine ⟨by omega,by omega,?_⟩
  intro v hv hva hvb
  have hvm : v ∈ M.atoms := (union_subset hS.1.1 hT.1.1) hv
  have hbound := (Mole.degIn_le_deg M (S ∪ T) v).trans (Mole.deg_le_four M hM hvm)
  rcases mem_union.mp hv with hv | hv
  · have hd := hS.1.2.2.2.2.2.2.2.2.1 v hv hva hvb
    have hle := degIn_mono M (show S ⊆ S ∪ T from subset_union_left) v
    omega
  · have hd := hT.1.2.2.2.2.2.2.2.2.1 v hv hva hvb
    have hle := degIn_mono M (show T ⊆ S ∪ T from subset_union_right) v
    omega

end WaveTurbulence.Vine
