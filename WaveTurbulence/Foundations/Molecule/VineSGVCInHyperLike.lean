/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperGapObjects
public import WaveTurbulence.Foundations.Molecule.VineHyperBothJoints
public import WaveTurbulence.Foundations.Molecule.VineHyperMissingJoint
public import WaveTurbulence.Foundations.Molecule.VineLocalDartGaps
public import WaveTurbulence.Foundations.Molecule.VineEraseBondDecoration
public import WaveTurbulence.Foundations.Molecule.VineSGVCInVC
import Mathlib.Tactic

/-! # Ordinary SG VC classification inside an LG/ZG designated hyper-object -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- TARGET subsetvc, ordinary inner-object clause in an outer HV/HVC.
If both outer joints are selected the inner VC is a single double bond;
otherwise the external closing bond is deleted and the exact local object,
decoration and gap are transported to the checked outer-VC theorem. -/
theorem SG_VC_in_hyperLike (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V} (R : HyperLikeRealization M U a b)
    (hA : IsVC M A x y) (hAU : A ⊆ U)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms,M.deg v=4 → c v=0)
    {r r' : Mom d} (hr : R.IsGap L w κ r) (hr' : M.IsBlockGap L w κ A x r')
    (houter : Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)
    (hsmall : Molecule.gapKind L γ η r'=.SG) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 ∨ M.IsVine .V A x y := by
  by_cases hboth : a ∈ A ∧ b ∈ A
  · have hU := hyperLike_iff_realization.mpr ⟨R⟩
    have hAe := block_in_hyperLike_both_joints_atoms M hM hU hA.1 hAU hboth.1 hboth.2
    have hcard : A.card=2 := by rw [hAe,Finset.card_pair R.adjoint.1.2.2.2.1]
    rcases isVC_doubleChain_of_card_le_three hA (by omega) with hD | hD
    · exact Or.inl hD
    · have hh := doubleChain_card hD
      omega
  · let F := eraseBond_local_embedding M R.added A
      (bond_external_of_missing_joint M R.added R.ends_eq hboth)
    have hne := ends_distinct_of_pair M R.added R.ends_eq R.adjoint.1.2.2.2.1
    have hN := eraseBond_isMolecule M hM R.added hne
    obtain ⟨cN,hκN,hcN⟩ := eraseBond_decoration_exists M hM R.added hne L w c κ hκ hc
    have hAN := (F.isVC_iff A (Finset.Subset.refl _) x y).mpr hA
    have hGN := (F.blockGap_iff A (Finset.Subset.refl _) L w κ x r').mpr hr'
    rcases SG_VC_in_VC (Mole.eraseBond M R.added) hN hAN R.adjoint hAU
      L γ η w cN (fun z => κ z.1) hκN hcN hr hGN houter hsmall with hD | hD | hV
    · exact Or.inl (F.doubleChain_to hD (Finset.Subset.refl _))
    · exact Or.inr (Or.inl (F.doubleChain_to hD (Finset.Subset.refl _)))
    · exact Or.inr (Or.inr ((F.isVine_iff .V A (Finset.Subset.refl _) x y).mp hV))

end WaveTurbulence.Vine
