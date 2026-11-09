/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineHyperMissingJoint
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperInVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLocalDartHyper
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.VineLocalDartObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.VineLocalDartObjects
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineHyperMissingJoint`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Hyper-object containment when an outer closing bond is external to the inner group 

**Low-range change (L6-HDS).** The adjoint/inner alternative "vine (V)" of main is a T-vine (N3 Cor 1.16′(2), via
`Src.DSInputs`, proved by L3: `Src.DSInputs.holds`); transports of `IsTVine` along local dart
embeddings are L6-HTV's `LocalDartEmbedding.isVine_iffT`. The localization steps are main's, ported.-/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc, proper endpoint case for an outer HV/HVC: an inner
hyper-vine-like object missing either outer joint has designated adjoint
two double bonds or Vine V. Deleting the external outer closing bond
transports all actual internal darts to the checked outer-VC classification. -/
theorem hyperLike_in_hyperLike_missing_joint_adjoint (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V} (hU : Src.IsHV Src.γL M U a b ∨ Src.IsHVC Src.γL M U a b)
    (hA : Src.IsHV Src.γL M A x y ∨ Src.IsHVC Src.γL M A x y) (hAU : A ⊆ U) (hmiss : ¬(a ∈ A ∧ b ∈ A)) :
    ∃ f : D,M.ends f=s(x,y) ∧
      (DoubleChain (Mole.eraseBond M f) A x y 2 ∨ (Mole.eraseBond M f).IsTVine A x y) := by
  obtain ⟨e,he,hVC⟩ := hyperLike_iff_adjoint_VC.mp hU
  let F := eraseBond_local_embedding M e A (bond_external_of_missing_joint M e he hmiss)
  have hN := eraseBond_isMolecule M hM e (ends_distinct_of_pair M e he hVC.1.2.2.2.1)
  have hAN : Src.IsHV Src.γL (Mole.eraseBond M e) A x y ∨ Src.IsHVC Src.γL (Mole.eraseBond M e) A x y :=
    (F.hyperLike_iffL x y).mpr hA
  obtain ⟨f,hf,hclass⟩ := hyperLike_in_VC_adjoint (Mole.eraseBond M e) hN hAN hVC hAU
  refine ⟨F.toFun f,(F.ends_eq f).trans hf,?_⟩
  rcases hclass with hD | hV
  · exact Or.inl ((F.eraseBond f).doubleChain_to hD (Finset.Subset.refl _))
  · exact Or.inr (((F.eraseBond f).isVine_iffT A (Finset.Subset.refl _) x y).mp hV)

end WaveTurbulence.GammaLow.FinalCount.H
