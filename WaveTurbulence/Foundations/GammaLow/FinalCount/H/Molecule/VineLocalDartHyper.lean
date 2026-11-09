/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineLocalDartHyper
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperAdjointVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineLocalDartHyper`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Local dart identifications preserve designated hyper-adjoint objects -/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
variable {V D E : Type*} [DecidableEq V] [Fintype D] [Fintype E] [DecidableEq D] [DecidableEq E]
    {M : Molecule V D} {N : Molecule V E} {A : Finset V}
namespace LocalDartEmbedding
open WaveTurbulence.Vine.LocalDartEmbedding
variable (F : LocalDartEmbedding M N A)

include F in
/-- The existential HV/HVC classification is preserved by identifying all
actual internal darts. Matched designated bond deletions are transported
before applying the exact VC equivalence. -/
theorem hyperLike_iffL (a b : V) :
    (Src.IsHV Src.γL N A a b ∨ Src.IsHVC Src.γL N A a b) ↔ (Src.IsHV Src.γL M A a b ∨ Src.IsHVC Src.γL M A a b) := by
  constructor
  · intro hN
    obtain ⟨f,hf,hVC⟩ := hyperLike_iff_adjoint_VC.mp hN
    apply hyperLike_iff_adjoint_VC.mpr
    exact ⟨F.toFun f,(F.ends_eq f).trans hf,((F.eraseBond f).isVC_iffL A (Finset.Subset.refl _) a b).mp hVC⟩
  · intro hM
    obtain ⟨f,hf,hVC⟩ := hyperLike_iff_adjoint_VC.mp hM
    have hfi : M.InGroup A f := by
      rcases Sym2.eq_iff.mp hf with hh | hh
      · exact ⟨hh.1.symm ▸ hVC.1.2.1,hh.2.symm ▸ hVC.1.2.2.1⟩
      · exact ⟨hh.1.symm ▸ hVC.1.2.2.1,hh.2.symm ▸ hVC.1.2.1⟩
    obtain ⟨g,hg⟩ := F.surjective_internal f hfi
    have hgN : N.ends g=s(a,b) := by
      rw [← F.ends_eq,hg]
      exact hf
    cases hg
    exact hyperLike_iff_adjoint_VC.mpr
      ⟨g,hgN,((F.eraseBond g).isVC_iffL A (Finset.Subset.refl _) a b).mpr hVC⟩

alias _root_.WaveTurbulence.Vine.LocalDartEmbedding.hyperLike_iffL := _root_.WaveTurbulence.GammaLow.FinalCount.H.LocalDartEmbedding.hyperLike_iffL
end LocalDartEmbedding
end WaveTurbulence.GammaLow.FinalCount.H
