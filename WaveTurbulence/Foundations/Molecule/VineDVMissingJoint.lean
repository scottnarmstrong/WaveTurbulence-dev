/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineDVDegrees
public import WaveTurbulence.Foundations.Molecule.VineTwoJointSeparator
public import WaveTurbulence.Foundations.Molecule.VineHyperVertexConnected
import Mathlib.Tactic

/-! # Objects missing a DV joint lie in one branch -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- Primitive two-joint separator localization in the two branches of a DV. -/
theorem DV_missing_joint_side (M : Molecule V D) (hM : M.IsMolecule)
    {S T A : Finset V} {a b : V} (hS : M.IsVine .V S a b) (hT : M.IsVine .V T a b)
    (hAU : A ⊆ S ∪ T) (hmiss : ¬(a ∈ A ∧ b ∈ A))
    (hconn : ∀ z,z=a ∨ z=b → GroupConnected M (A.erase z)) : A ⊆ S ∨ A ⊆ T := by
  by_cases hb : b ∈ A
  · have ha : a ∉ A := fun ha => hmiss ⟨ha,hb⟩
    exact two_groups_missing_right_joint_side M hM S T A b a hS.1.2.2.1 hT.1.2.2.1
      hS.1.2.2.2.1.symm hT.1.1
      (fun v hv hvb hva => hT.1.2.2.2.2.2.2.2.2.1 v hv hva hvb) hAU ha (hconn b (Or.inr rfl))
  · exact two_groups_missing_right_joint_side M hM S T A a b hS.1.2.1 hT.1.2.1
      hS.1.2.2.2.1 hT.1.1 hT.1.2.2.2.2.2.2.2.2.1 hAU hb (hconn a (Or.inl rfl))

omit [DecidableEq D] in
/-- TARGET subsetvc, ordinary inner VC in a DV missing either joint:
its endpoint-removal connectivity localizes it in one actual type-V branch. -/
theorem VC_in_DV_missing_joint_side (M : Molecule V D) (hM : M.IsMolecule)
    {S T A : Finset V} {a b x y : V} (hS : M.IsVine .V S a b) (hT : M.IsVine .V T a b)
    (hi : S ∩ T={a,b}) (hA : IsVC M A x y) (hAU : A ⊆ S ∪ T)
    (hmiss : ¬(a ∈ A ∧ b ∈ A)) : A ⊆ S ∨ A ⊆ T := by
  have hd := isDV_degree_profile M hM (show IsDV M (S ∪ T) a b from ⟨S,T,hS,hT,hi,rfl⟩)
  apply DV_missing_joint_side M hM hS hT hAU hmiss
  intro z hz
  by_cases hzA : z ∈ A
  · have hdz : M.degIn (S ∪ T) z=3 := hz.elim (fun h => h.symm ▸ hd.1) (fun h => h.symm ▸ hd.2.1)
    have hle := degIn_mono M hAU z
    have hzj : z=x ∨ z=y := by
      by_contra hh
      have h4 := hA.1.2.2.2.2.2.2.2.2.1 z hzA (not_or.mp hh).1 (not_or.mp hh).2
      omega
    exact isVC_erase_joint_connected hA hzj
  · rw [Finset.erase_eq_self.mpr hzA]
    exact isVC_connected hA

/-- Every contained HV/HVC missing a DV joint likewise lies in one branch;
its stronger one-atom connectivity requires no decoration hypothesis. -/
theorem hyperLike_in_DV_missing_joint_side (M : Molecule V D) (hM : M.IsMolecule)
    {S T A : Finset V} {a b x y : V} (hS : M.IsVine .V S a b) (hT : M.IsVine .V T a b)
    (hA : IsHV M A x y ∨ IsHVC M A x y) (hAU : A ⊆ S ∪ T)
    (hmiss : ¬(a ∈ A ∧ b ∈ A)) : A ⊆ S ∨ A ⊆ T :=
  DV_missing_joint_side M hM hS hT hAU hmiss (fun z _hz => hyperLike_erase_connected M hA z)

end WaveTurbulence.Vine
