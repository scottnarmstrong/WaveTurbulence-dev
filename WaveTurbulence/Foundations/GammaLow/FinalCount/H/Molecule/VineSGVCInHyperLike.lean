/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineSGVCInHyperLike
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperBothJoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperMissingJoint
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGVCInVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.VineLocalDartObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.VineLocalDartObjects
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineSGVCInHyperLike`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Ordinary SG VC classification inside an LG/ZG designated hyper-object 

**Low-range change (L6-HDS).** The adjoint/inner alternative "vine (V)" of main is a T-vine (N3 Cor 1.16′(2), via
`Src.DSInputs`, proved by L3: `Src.DSInputs.holds`); transports of `IsTVine` along local dart
embeddings are L6-HTV's `LocalDartEmbedding.isVine_iffT`. The localization steps are main's, ported.-/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- TARGET subsetvc, ordinary inner-object clause in an outer HV/HVC.
If both outer joints are selected the inner VC is a single double bond;
otherwise the external closing bond is deleted and the exact local object,
decoration and gap are transported to the checked outer-VC theorem. -/
theorem SG_VC_in_hyperLike (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V} (R : Src.HyperLikeRealization Src.γL M U a b)
    (hA : Src.IsVC Src.γL M A x y) (hAU : A ⊆ U)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms,M.deg v=4 → c v=0)
    {r r' : Mom d} (hr : R.IsGap L w κ r) (hr' : M.IsBlockGap L w κ A x r')
    (houter : Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)
    (hsmall : Molecule.gapKind L γ η r'=.SG) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 ∨ M.IsTVine A x y := by
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
    have hAN := (F.isVC_iffL A (Finset.Subset.refl _) x y).mpr hA
    have hGN := (F.blockGap_iff A (Finset.Subset.refl _) L w κ x r').mpr hr'
    rcases SG_VC_in_VC (Mole.eraseBond M R.added) hN hAN R.adjoint hAU
      L γ η w cN (fun z => κ z.1) hκN hcN hr hGN houter hsmall with hD | hD | hV
    · exact Or.inl (F.doubleChain_to hD (Finset.Subset.refl _))
    · exact Or.inr (Or.inl (F.doubleChain_to hD (Finset.Subset.refl _)))
    · exact Or.inr (Or.inr ((F.isVine_iffT A (Finset.Subset.refl _) x y).mp hV))

end WaveTurbulence.GammaLow.FinalCount.H
