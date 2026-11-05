/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineLocalDartHyper
public import WaveTurbulence.Foundations.Molecule.VineEraseBondMolecule
public import WaveTurbulence.Foundations.Molecule.VineHyperInVC
import Mathlib.Tactic

/-! # Hyper-object containment when an outer closing bond is external to the inner group -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
/-- A specified nonloop endpoint pair has distinct actual endpoint atoms. -/
theorem ends_distinct_of_pair (M : Molecule V D) (e : D) {a b : V}
    (he : M.ends e=s(a,b)) (hab : a ≠ b) : M.atom e ≠ M.atom (M.mate e) := by
  rcases Sym2.eq_iff.mp he with hh | hh <;> rw [hh.1,hh.2]
  · exact hab
  · exact hab.symm

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
/-- If a selected atomic group misses either endpoint, the designated
bond is external to that group. -/
theorem bond_external_of_missing_joint (M : Molecule V D) (e : D) {A : Finset V} {a b : V}
    (he : M.ends e=s(a,b)) (hmiss : ¬(a ∈ A ∧ b ∈ A)) : ¬M.InGroup A e := by
  intro hi
  rcases Sym2.eq_iff.mp he with hh | hh
  · exact hmiss ⟨hh.1 ▸ hi.1,hh.2 ▸ hi.2⟩
  · exact hmiss ⟨hh.2 ▸ hi.2,hh.1 ▸ hi.1⟩

/-- TARGET subsetvc, proper endpoint case for an outer HV/HVC: an inner
hyper-vine-like object missing either outer joint has designated adjoint
two double bonds or Vine V. Deleting the external outer closing bond
transports all actual internal darts to the checked outer-VC classification. -/
theorem hyperLike_in_hyperLike_missing_joint_adjoint (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V} (hU : IsHV M U a b ∨ IsHVC M U a b)
    (hA : IsHV M A x y ∨ IsHVC M A x y) (hAU : A ⊆ U) (hmiss : ¬(a ∈ A ∧ b ∈ A)) :
    ∃ f : D,M.ends f=s(x,y) ∧
      (DoubleChain (Mole.eraseBond M f) A x y 2 ∨ (Mole.eraseBond M f).IsVine .V A x y) := by
  obtain ⟨e,he,hVC⟩ := hyperLike_iff_adjoint_VC.mp hU
  let F := eraseBond_local_embedding M e A (bond_external_of_missing_joint M e he hmiss)
  have hN := eraseBond_isMolecule M hM e (ends_distinct_of_pair M e he hVC.1.2.2.2.1)
  have hAN : IsHV (Mole.eraseBond M e) A x y ∨ IsHVC (Mole.eraseBond M e) A x y :=
    (F.hyperLike_iff x y).mpr hA
  obtain ⟨f,hf,hclass⟩ := hyperLike_in_VC_adjoint (Mole.eraseBond M e) hN hAN hVC hAU
  refine ⟨F.toFun f,(F.ends_eq f).trans hf,?_⟩
  rcases hclass with hD | hV
  · exact Or.inl ((F.eraseBond f).doubleChain_to hD (Finset.Subset.refl _))
  · exact Or.inr (((F.eraseBond f).isVine_iff .V A (Finset.Subset.refl _) x y).mp hV)

end WaveTurbulence.Vine
