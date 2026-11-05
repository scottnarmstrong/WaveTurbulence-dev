/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineDVOrdinary
public import WaveTurbulence.Foundations.Molecule.VineHyperBothJoints
public import WaveTurbulence.Foundations.Molecule.VineHyperSingleVine
public import WaveTurbulence.Foundations.Molecule.VineSameJointProfile
import Mathlib.Tactic

/-! # Hyper-object structural classification in a double vine -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A contained hyper-block selecting both DV joints equals the entire DV,
by exact nested-degree closure in the connected outer group. -/
theorem hyperBlock_in_DV_both_joints_eq (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V} (hU : IsDV M U a b)
    (hA : Mole.IsHyperBlock M A x y) (hAU : A ⊆ U) (ha : a ∈ A) (hb : b ∈ A) : A=U := by
  have hdU := isDV_degree_profile M hM hU
  have hconn := isDV_connected hU
  have hdA := Mole.hyperBlock_degrees M hA
  obtain ⟨S,T,hS,_hT,_hi,_hUnion⟩ := hU
  obtain ⟨e,_he,hB⟩ := hA
  have hj := joints_eq_of_two_low_degrees M hAU ha hb hS.1.2.2.2.1 hB.2.2.2.1
    hdU.1.le hdU.2.1.le hdA.2.2
  exact nested_degree_eq_of_connected M hAU ⟨a,ha⟩ hconn
    (same_joint_profile_degrees M 3 hAU hj hdA hdU)

/-- A DV cannot itself be an HV/HVC. Otherwise either of its type-V
branches, containing both hyper-object joints, would have just two atoms. -/
theorem isDV_not_hyperLike (M : Molecule V D) (hM : M.IsMolecule)
    {U : Finset V} {a b x y : V} (hU : IsDV M U a b) : ¬(IsHV M U x y ∨ IsHVC M U x y) := by
  intro hH
  have hdU := isDV_degree_profile M hM hU
  obtain ⟨e,he,hVC⟩ := hyperLike_iff_adjoint_VC.mp hH
  have hdH := Mole.hyperBlock_degrees M (show Mole.IsHyperBlock M U x y from ⟨e,he,hVC.1⟩)
  obtain ⟨S,T,hS,hT,_hi,rfl⟩ := hU
  have ha : a ∈ S ∪ T := mem_union_left _ hS.1.2.1
  have hb : b ∈ S ∪ T := mem_union_left _ hS.1.2.2.1
  have hj := joints_eq_of_two_low_degrees M (Subset.refl (S ∪ T)) ha hb hS.1.2.2.2.1 hVC.1.2.2.2.1
    hdU.1.le hdU.2.1.le hdH.2.2
  have hjS : ({x,y} : Finset V) ⊆ S := by
    rw [hj]
    intro v hv
    rcases mem_insert.mp hv with hva | hvb
    · exact hva.symm ▸ hS.1.2.1
    · exact (mem_singleton.mp hvb).symm ▸ hS.1.2.2.1
  have hEq := block_in_hyperLike_both_joints_atoms M hM hH hS.1 subset_union_left
    (hjS (mem_insert_self _ _)) (hjS (mem_insert_of_mem (mem_singleton_self _)))
  have hc : S.card=2 := by rw [hEq,card_pair hVC.1.2.2.2.1]
  have hbad := isVine_typeI_of_card_lt_four hS (by omega)
  cases hbad

/-- TARGET Lemma subsetvc, complete inner-HV/HVC classification in a DV.
Both-joint selection is impossible, so geometric localization and the checked
single-vine theorem construct the designated adjoint form. -/
theorem hyperLike_in_DV_adjoint (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V} (hU : IsDV M U a b)
    (hA : IsHV M A x y ∨ IsHVC M A x y) (hAU : A ⊆ U) :
    ∃ e : D,M.ends e=s(x,y) ∧
      (DoubleChain (Mole.eraseBond M e) A x y 2 ∨ (Mole.eraseBond M e).IsVine .V A x y) := by
  have hH : Mole.IsHyperBlock M A x y := by
    obtain ⟨e,he,hVC⟩ := hyperLike_iff_adjoint_VC.mp hA
    exact ⟨e,he,hVC.1⟩
  have hmiss : ¬(a ∈ A ∧ b ∈ A) := by
    intro hab
    have he := hyperBlock_in_DV_both_joints_eq M hM hU hH hAU hab.1 hab.2
    subst A
    exact isDV_not_hyperLike M hM hU hA
  obtain ⟨S,T,hS,hT,_hi,rfl⟩ := hU
  rcases hyperLike_in_DV_missing_joint_side M hM hS hT hA hAU hmiss with hAS | hAT
  · exact hyperLike_in_single_vine_adjoint M hM hS hAS hA
  · exact hyperLike_in_single_vine_adjoint M hM hT hAT hA

end WaveTurbulence.Vine
