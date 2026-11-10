/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineHyperVertexConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineBranchingEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainCounts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineEraseChainIngredient
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperAdjointVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSmallVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineHyperVertexConnected`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Hyper-vine-like objects have no separating atom -/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET defvine/subsetvc: removing any one atom from an HV or HVC
leaves its atom group connected. The retained designated closing bond joins
the surviving chain ends; every other atom reaches one of those ends. -/
theorem hyperLike_erase_connected (M : Molecule V D) {S : Finset V} {a b : V}
    (h : Src.IsHV Src.γL M S a b ∨ Src.IsHVC Src.γL M S a b) (z : V) : GroupConnected M (S.erase z) := by
  obtain ⟨e,he,hB,n,hchain⟩ := hyperLike_iff_adjoint_VC.mp h
  have hab : M.Adj a b := by
    rcases Sym2.eq_iff.mp he with he | he
    · exact ⟨e,he.1,he.2⟩
    · exact ⟨M.mate e,he.2,by rw [M.mate_mate]; exact he.1⟩
  have bridge (haz : a ≠ z) (hbz : b ≠ z) : (Mole.induced M (S.erase z)).SameComponent a b :=
    Relation.EqvGen.rel _ _ ((Mole.induced_adj_iff M (S.erase z) a b).mpr
      ⟨hab,mem_erase.mpr ⟨haz,hB.2.1⟩,mem_erase.mpr ⟨hbz,hB.2.2.1⟩⟩)
  intro u hu v hv
  have hu' := chain_erase_endpoint_reach hchain u hu
  have hv' := chain_erase_endpoint_reach hchain v hv
  rcases hu' with ⟨haz,hau⟩ | ⟨hbz,hbu⟩ <;> rcases hv' with ⟨haz',hav⟩ | ⟨hbz',hbv⟩
  · exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (eraseBond_induced_path M e _ hau))
      (eraseBond_induced_path M e _ hav)
  · exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (eraseBond_induced_path M e _ hau))
      (Relation.EqvGen.trans _ _ _ (bridge haz hbz') (eraseBond_induced_path M e _ hbv))
  · exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (eraseBond_induced_path M e _ hbu))
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (bridge haz' hbz)) (eraseBond_induced_path M e _ hav))
  · exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (eraseBond_induced_path M e _ hbu))
      (eraseBond_induced_path M e _ hbv)

end WaveTurbulence.GammaLow.FinalCount.H
