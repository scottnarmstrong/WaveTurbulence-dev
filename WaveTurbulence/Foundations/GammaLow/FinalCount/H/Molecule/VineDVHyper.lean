/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineDVHyper
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVOrdinary
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperBothJoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperSingleVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.DV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineDVHyper`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Hyper-object structural classification in a double vine 

**Low-range change (L6-HDS).** The DV is a DV′ of the low family (branches: T-vines with `σ = 1`); the adjoint
alternative "vine (V)" is a T-vine (`hyperLike_in_single_vine_adjoint`, N3 Cor 1.16′(2) via `Src.DSInputs`).
-/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A contained hyper-block selecting both DV joints equals the entire DV,
by exact nested-degree closure in the connected outer group. -/
theorem hyperBlock_in_DV_both_joints_eq (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V} (hU : Src.IsDV Src.γL M U a b)
    (hA : Mole.IsHyperBlock M A x y) (hAU : A ⊆ U) (ha : a ∈ A) (hb : b ∈ A) : A=U := by
  have hconn := isDV_connected hU
  have hdA := Mole.hyperBlock_degrees M hA
  obtain ⟨hσ, S,T,hS,hT,hi,rfl⟩ := hU
  have hdU := DS.dv_degree_profile hM hσ (Src.isBlock_of_isSomeVine hS) (Src.isBlock_of_isSomeVine hT) hi
  obtain ⟨e,_he,hB⟩ := hA
  have hj := joints_eq_of_two_low_degrees M hAU ha hb (Src.isBlock_of_isSomeVine hS).2.2.2.1 hB.2.2.2.1
    hdU.1.le hdU.2.1.le hdA.2.2
  exact nested_degree_eq_of_connected M hAU ⟨a,ha⟩ hconn
    (same_joint_profile_degrees M 3 hAU hj hdA hdU)

/-- A DV′ cannot itself be an HV/HVC. Otherwise either of its branches (T-vines, at least five atoms), containing both
hyper-object joints, would have just two atoms. -/
theorem isDV_not_hyperLike (M : Molecule V D) (hM : M.IsMolecule)
    {U : Finset V} {a b x y : V} (hU : Src.IsDV Src.γL M U a b) : ¬(Src.IsHV Src.γL M U x y ∨ Src.IsHVC Src.γL M U x y) := by
  intro hH
  obtain ⟨R⟩ := DS.hyperLike_realization hH
  have hVC := R.adjoint
  have hdH := Mole.hyperBlock_degrees M (show Mole.IsHyperBlock M U x y from ⟨R.added, R.ends_eq, R.adjoint.1⟩)
  obtain ⟨hσ, S,T,hS,hT,_hi,rfl⟩ := hU
  have hdU := DS.dv_degree_profile hM hσ (Src.isBlock_of_isSomeVine hS) (Src.isBlock_of_isSomeVine hT) _hi
  have ha : a ∈ S ∪ T := mem_union_left _ (Src.isBlock_of_isSomeVine hS).2.1
  have hb : b ∈ S ∪ T := mem_union_left _ (Src.isBlock_of_isSomeVine hS).2.2.1
  have hj := joints_eq_of_two_low_degrees M (Subset.refl (S ∪ T)) ha hb (Src.isBlock_of_isSomeVine hS).2.2.2.1 hVC.1.2.2.2.1
    hdU.1.le hdU.2.1.le hdH.2.2
  have hjS : ({x,y} : Finset V) ⊆ S := by
    rw [hj]
    intro v hv
    rcases mem_insert.mp hv with hva | hvb
    · exact hva.symm ▸ (Src.isBlock_of_isSomeVine hS).2.1
    · exact (mem_singleton.mp hvb).symm ▸ (Src.isBlock_of_isSomeVine hS).2.2.1
  have hEq := block_in_hyperLike_both_joints_atoms M hM hH (Src.isBlock_of_isSomeVine hS) subset_union_left
    (hjS (mem_insert_self _ _)) (hjS (mem_insert_of_mem (mem_singleton_self _)))
  have hc : S.card=2 := by rw [hEq,card_pair hVC.1.2.2.2.1]
  have h5 := DS.isTVine_card (DS.isTVine_of_sigma_one hS hσ)
  omega

theorem hyperLike_in_DV_adjoint (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V} (hU : Src.IsDV Src.γL M U a b)
    (hA : Src.IsHV Src.γL M A x y ∨ Src.IsHVC Src.γL M A x y) (hAU : A ⊆ U) :
    ∃ e : D,M.ends e=s(x,y) ∧
      (DoubleChain (Mole.eraseBond M e) A x y 2 ∨ (Mole.eraseBond M e).IsTVine A x y) := by
  have hH : Mole.IsHyperBlock M A x y := by
    obtain ⟨R⟩ := DS.hyperLike_realization hA
    exact ⟨R.added, R.ends_eq, R.adjoint.1⟩
  have hmiss : ¬(a ∈ A ∧ b ∈ A) := by
    intro hab
    have he := hyperBlock_in_DV_both_joints_eq M hM hU hH hAU hab.1 hab.2
    subst A
    exact isDV_not_hyperLike M hM hU hA
  obtain ⟨-, S,T,hS,hT,_hi,rfl⟩ := hU
  rcases hyperLike_in_DV_missing_joint_side M hM hS hT hA hAU hmiss with hAS | hAT
  · exact hyperLike_in_single_vine_adjoint M hS hAS hA
  · exact hyperLike_in_single_vine_adjoint M hT hAT hA

end WaveTurbulence.GammaLow.FinalCount.H
