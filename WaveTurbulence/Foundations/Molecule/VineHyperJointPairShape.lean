/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineVCJointEdge
public import WaveTurbulence.Foundations.Molecule.VineHyperBothJoints
public import WaveTurbulence.Foundations.Molecule.VineHyperGapObjects
import Mathlib.Tactic

/-! # A both-joints ordinary piece in a hyper-object forces a type-V adjoint -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Deleting one designated nonloop bond from a degree-two joint pair
leaves degree one at the first joint, independent of mate orientation. -/
theorem eraseBond_pair_degree_one (M : Molecule V D) (e : D) {a b : V}
    (he : M.ends e=s(a,b)) (hab : a ≠ b) (hd : M.degIn {a,b} a=2) :
    (Mole.eraseBond M e).degIn {a,b} a=1 := by
  rcases Sym2.eq_iff.mp he with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have hh := Mole.eraseBond_degIn_endpoint M e ha hb hab
      (mem_insert_self a {b}) (mem_insert_of_mem (mem_singleton_self b))
    omega
  · have hh := Mole.eraseBond_degIn_endpoint M (M.mate e) hb
      (by rw [M.mate_mate]; exact ha) hab (mem_insert_self a {b}) (mem_insert_of_mem (mem_singleton_self b))
    rw [Mole.eraseBond_mate_degIn] at hh
    omega

/-- An actual ordinary vine selecting both outer hyper-object joints is
exactly their type-I double bond; the designated outer adjoint is type V.
This is structural and needs no decoration or gap assumption. -/
theorem ordinary_vine_in_hyperLike_both_joint_shape (M : Molecule V D) (hM : M.IsMolecule)
    {U P : Finset V} {a b x y : V} (R : HyperLikeRealization M U a b)
    (hP : IsSomeVine M P x y) (hPU : P ⊆ U) (ha : a ∈ P) (hb : b ∈ P) :
    P={a,b} ∧ M.IsVine .I P x y ∧ (Mole.eraseBond M R.added).IsVine .V U a b := by
  obtain ⟨X,hX⟩ := hP
  have hHyper : IsHV M U a b ∨ IsHVC M U a b := hyperLike_iff_realization.mpr ⟨R⟩
  have hAtoms := block_in_hyperLike_both_joints_atoms M hM hHyper hX.1 hPU ha hb
  have hcard : P.card=2 := by rw [hAtoms,card_pair R.adjoint.1.2.2.2.1]
  have htype := isVine_typeI_of_card_lt_four hX (by omega)
  subst X
  have haPair : a=x ∨ a=y := by
    have hh := ha
    rw [typeI_atoms hX] at hh
    simpa only [mem_insert,mem_singleton] using hh
  have hdeg : M.degIn P a=2 := haPair.elim
    (fun h => h.symm ▸ (Mole.block_joint_degrees M hX.1).1)
    (fun h => h.symm ▸ (Mole.block_joint_degrees M hX.1).2)
  rw [hAtoms] at hdeg
  have hOne := eraseBond_pair_degree_one M R.added R.ends_eq R.adjoint.1.2.2.2.1 hdeg
  exact ⟨hAtoms,hX,VC_joint_pair_degree_one_isVineV _ R.adjoint hOne⟩

end WaveTurbulence.Vine
