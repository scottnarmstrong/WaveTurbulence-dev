/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceOneJointPairFalse
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineBranchingEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainCounts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVMissingJoint
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineEraseChainIngredient
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperAdjointVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperBothJoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperVertexConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSmallVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineTwoJointSeparator
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceContainerAbsorb
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDVContainer
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDVUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDiamondClosed
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDiamondContradiction
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDiamondVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceHyperAbsorb
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceHyperBlockFalse
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceHyperDiamondObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceHyperUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceMaximalObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectFinite
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceOneJointContradiction
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceOneJointUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceSwapObject
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUnionAtoms
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUnionContradiction
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUnionDV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUnionEligible
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjectBridge
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceOneJointPairFalse`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Orientation-free form: two selected ordinary objects meeting in a single common joint whose
union is a block or a hyper-block cannot both be selected. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open SourceVine Finset

theorem orient_selected {w d : ℕ} (G : Garden w) (hM : G.molecule.IsMolecule) {L γ η : ℝ}
    {base : Mom d} {κ : GardenDart G → (Fin d → ℤ)} {c0 : GBranch G.tree → Mom d}
    (hκ : G.molecule.IsDecoration L base c0 κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c0 v = 0)
    {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))} {collection : Set (Src.Object Src.γL G.molecule)}
    (hc : Src.IsSourceSecondCollection Src.γL G L γ η base κ F omitted collection)
    {P : Src.Object Src.γL G.molecule} (hPm : P ∈ collection) (hPvc : ∃ h, P.shape = .vc h)
    {a c : GBranch G.tree} (hset : ({P.upper, P.lower} : Finset _) = {a, c}) :
    ∃ P' : Src.Object Src.γL G.molecule, P' ∈ collection ∧ (∃ h, P'.shape = .vc h) ∧ P'.atoms = P.atoms ∧
      P'.upper = a ∧ P'.lower = c := by
  rcases Mole.finset_pair_eq_pair_iff.mp hset with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨P, hPm, hPvc, rfl, h1, h2⟩
  · exact ⟨swapVC P hPvc, swapVC_mem G hM hκ hc0 hc hPm hPvc, (swapVC_atoms P hPvc).2.2.2,
      rfl, h2, h1⟩

theorem one_joint_pair_false {w d : ℕ} (G : Garden w) (hM : G.molecule.IsMolecule) {L γ η : ℝ}
    {base : Mom d} {κ : GardenDart G → (Fin d → ℤ)} {c0 : GBranch G.tree → Mom d}
    (hκ : G.molecule.IsDecoration L base c0 κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c0 v = 0)
    {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))} {collection : Set (Src.Object Src.γL G.molecule)}
    (hc : Src.IsSourceSecondCollection Src.γL G L γ η base κ F omitted collection)
    {P Q : Src.Object Src.γL G.molecule} (hPm : P ∈ collection) (hQm : Q ∈ collection)
    (hPvc : ∃ h, P.shape = .vc h) (hQvc : ∃ h, Q.shape = .vc h)
    {a b c : GBranch G.tree} (hP : ({P.upper, P.lower} : Finset _) = {a, c})
    (hQ : ({Q.upper, Q.lower} : Finset _) = {b, c}) (hPQ : P.atoms ∩ Q.atoms = {c})
    (hU : G.molecule.IsBlock (P.atoms ∪ Q.atoms) a b ∨
      Mole.IsHyperBlock G.molecule (P.atoms ∪ Q.atoms) a b) : False := by
  obtain ⟨P', hP'm, hP'vc, hP'at, hP'u, hP'l⟩ := orient_selected G hM hκ hc0 hc hPm hPvc hP
  obtain ⟨Q', hQ'm, hQ'vc, hQ'at, hQ'u, hQ'l⟩ := orient_selected G hM hκ hc0 hc hQm hQvc
    (a := c) (c := b) (hQ.trans (Finset.pair_comm b c))
  have hPQ' : P'.atoms ∩ Q'.atoms = {c} := by rw [hP'at, hQ'at]; exact hPQ
  obtain ⟨n, hPch0⟩ := object_vc_chain P' hP'vc
  obtain ⟨m, hQch0⟩ := object_vc_chain Q' hQ'vc
  have hPch : Src.Chain Src.γL G.molecule P'.atoms P'.upper c n := by rw [← hP'l]; exact hPch0
  have hQch : Src.Chain Src.γL G.molecule Q'.atoms c Q'.lower m := by rw [← hQ'u]; exact hQch0
  have hU' : G.molecule.IsBlock (P'.atoms ∪ Q'.atoms) P'.upper Q'.lower ∨
      Mole.IsHyperBlock G.molecule (P'.atoms ∪ Q'.atoms) P'.upper Q'.lower := by
    rw [hP'at, hQ'at, hP'u, hQ'l]; exact hU
  rcases hU' with hB | hH
  · exact one_joint_union_contradiction G hM hκ hc0 hc hP'm hQ'm hP'vc hQ'vc hP'l hQ'u hPch hQch
      hPQ' hB
  · exact one_joint_hyperblock_false G hM hκ hc0 hc hP'm hQ'm hP'vc hQ'vc hP'l hQ'u hPch hQch
      hPQ' hH

end WaveTurbulence.GammaLow.FinalCount.H
