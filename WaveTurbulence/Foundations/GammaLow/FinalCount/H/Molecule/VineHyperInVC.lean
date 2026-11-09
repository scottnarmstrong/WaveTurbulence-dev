/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineHyperInVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineEraseChainIngredient
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperSingleVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperVertexConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineHyperInVC`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Hyper-object localization and adjoint classification in an outer VC 

**Low-range change (L6-HDS).** The adjoint/inner alternative "vine (V)" of main is a T-vine (N3 Cor 1.16′(2), via
`Src.DSInputs`, proved by L3: `Src.DSInputs.holds`); transports of `IsTVine` along local dart
embeddings are L6-HTV's `LocalDartEmbedding.isVine_iffT`. The localization steps are main's, ported.-/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc, hyper-object localization in an outer VC. The closing
bond makes the inner object vertex connected, so no gap premise is needed. -/
theorem hyperLike_in_VC_ingredient (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V} (h : Src.IsHV Src.γL M A x y ∨ Src.IsHVC Src.γL M A x y)
    (hU : Src.IsVC Src.γL M U a b) (hAU : A ⊆ U) :
    ∃ n T p q,ChainIngredient M U a b n T p q ∧ A ⊆ T := by
  obtain ⟨hUB,n,hchain⟩ := hU
  obtain ⟨T,p,q,hT,hAT⟩ := erase_connected_in_chain_ingredient M hM
    (fun z => hyperLike_erase_connected M h z) hchain hUB hAU
  exact ⟨n,T,p,q,hT,hAT⟩

/-- TARGET subsetvc, hyper-object structural clause in any outer VC:
the designated adjoint is exactly two double bonds or a type-V vine.
All ingredient and cap data are constructed from source containment. -/
theorem hyperLike_in_VC_adjoint (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V} (h : Src.IsHV Src.γL M A x y ∨ Src.IsHVC Src.γL M A x y)
    (hU : Src.IsVC Src.γL M U a b) (hAU : A ⊆ U) :
    ∃ e : D,M.ends e=s(x,y) ∧
      (DoubleChain (Mole.eraseBond M e) A x y 2 ∨ (Mole.eraseBond M e).IsTVine A x y) := by
  obtain ⟨n,T,p,q,hT,hAT⟩ := hyperLike_in_VC_ingredient M hM h hU hAU
  obtain ⟨_hchain,hX,_hTU⟩ := chainIngredient_spec hT
  exact hyperLike_in_single_vine_adjoint M hX hAT h

end WaveTurbulence.GammaLow.FinalCount.H
