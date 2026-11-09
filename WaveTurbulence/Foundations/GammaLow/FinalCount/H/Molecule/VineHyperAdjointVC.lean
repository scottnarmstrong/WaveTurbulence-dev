/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineHyperAdjointVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineBranchingEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSmallVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineHyperAdjointVC`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # The exact designated-VC adjoint witness of a hyper-vine-like object -/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET defvine: an HV or HVC is exactly an object with a designated
joint bond whose deletion is a VC. A one-ingredient chain yields HV; at least
two ingredients yield HVC. The deleted actual bond is kept in the witness. -/
theorem hyperLike_iff_adjoint_VC {M : Molecule V D} {A : Finset V} {x y : V} :
    (Src.IsHV Src.γL M A x y ∨ Src.IsHVC Src.γL M A x y) ↔
      ∃ e : D,M.ends e=s(x,y) ∧ Src.IsVC Src.γL (Mole.eraseBond M e) A x y := by
  constructor
  · rintro (h | h)
    · obtain ⟨e,he,hV⟩ := h
      exact ⟨e,he,isSomeVine_isVC hV⟩
    · obtain ⟨e,he,hB,n,_hn,hC⟩ := h
      exact ⟨e,he,hB,n,hC⟩
  · rintro ⟨e,he,hB,n,hC⟩
    by_cases hn : n=1
    · subst n
      exact Or.inl ⟨e,he,chain_one_isSomeVine hC⟩
    · have hpos := chain_pos hC
      exact Or.inr ⟨e,he,hB,n,by omega,hC⟩

/-- The adjoint of a three-atom HV/HVC is exactly two concatenated double
bonds. This uses the source VC witness, not merely a degree-shaped triangle. -/
theorem hyperLike_three_atom_adjoint {M : Molecule V D} {A : Finset V} {x y : V}
    (h : Src.IsHV Src.γL M A x y ∨ Src.IsHVC Src.γL M A x y) (hcard : A.card=3) :
    ∃ e : D,M.ends e=s(x,y) ∧ DoubleChain (Mole.eraseBond M e) A x y 2 := by
  obtain ⟨e,he,hVC⟩ := hyperLike_iff_adjoint_VC.mp h
  rcases isVC_doubleChain_of_card_le_three hVC (by omega) with h1 | h2
  · have hc := doubleChain_card h1
    omega
  · exact ⟨e,he,h2⟩

end WaveTurbulence.GammaLow.FinalCount.H
