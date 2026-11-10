/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceHyperDiamondObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineBranchingEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainCounts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineEraseChainIngredient
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperAdjointVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperBothJoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperVertexConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSmallVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineTwoJointSeparator
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceContainerAbsorb
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDiamondClosed
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDiamondContradiction
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDiamondVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceMaximalObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectFinite
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceOneJointUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUnionContradiction
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUnionEligible
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjectBridge
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceHyperDiamondObjects`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Object-level hyper diamond: two selected vine-like objects with the same joints meeting
exactly in the joints, not nested, at least one of them a hyper-object: impossible. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open SourceVine Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem object_oh (O : Src.Object Src.γL M) : OH M O.atoms O.upper O.lower := by
  rcases O with ⟨S, a, b, sh⟩
  cases sh with
  | vc h => exact Or.inl h.1
  | hyper R => exact Or.inr ⟨R.added, R.ends_eq, R.adjoint.1⟩

theorem object_degIn_upper (O : Src.Object Src.γL M) :
    ((∃ h, O.shape = .vc h) → M.degIn O.atoms O.upper = 2) ∧
    ((∃ R, O.shape = .hyper R) → M.degIn O.atoms O.upper = 3) := by
  rcases O with ⟨S, a, b, sh⟩
  cases sh with
  | vc h =>
    refine ⟨fun _ => (Mole.block_joint_degrees M h.1).1, ?_⟩
    rintro ⟨R, hR⟩; cases hR
  | hyper R =>
    refine ⟨?_, fun _ => (Mole.hyperBlock_degrees M ⟨R.added, R.ends_eq, R.adjoint.1⟩).1⟩
    rintro ⟨h, hh⟩; cases hh

theorem object_diamond_false (hM : M.IsMolecule) {P Q : Src.Object Src.γL M}
    (hPQ : P.atoms ∩ Q.atoms = {P.upper, P.lower})
    (hQj : (Q.upper = P.upper ∧ Q.lower = P.lower) ∨ (Q.upper = P.lower ∧ Q.lower = P.upper))
    (hnest : ¬ P.atoms ⊆ Q.atoms) (hnest' : ¬ Q.atoms ⊆ P.atoms)
    (hhyp : (∃ R, P.shape = .hyper R) ∨ (∃ R, Q.shape = .hyper R)) : False := by
  have hQ : OH M Q.atoms P.upper P.lower := by
    rcases hQj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact object_oh Q
    · rw [← h1, ← h2]; exact (object_oh Q).swap
  have hdQ : M.degIn Q.atoms P.upper ≥ 2 := by
    have := hQ.basic; omega
  have hdP : M.degIn P.atoms P.upper ≥ 2 := by
    have := (object_oh P).basic; omega
  refine hyper_diamond_false hM (object_oh P) hQ hPQ ?_ hnest hnest'
  rcases hhyp with hP | hQh
  · have := (object_degIn_upper P).2 hP; omega
  · have h3 := (object_degIn_upper Q).2 hQh
    have hb := hQ.basic
    rcases hQj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at h3; omega
    · rw [h1] at h3
      omega


theorem object_oh_at (O : Src.Object Src.γL M) {c : V} (hO : O.upper = c ∨ O.lower = c) :
    ∃ a, OH M O.atoms c a ∧ ((∃ R, O.shape = .hyper R) → M.degIn O.atoms c = 3) ∧
      (M.degIn O.atoms c = 2 ∨ M.degIn O.atoms c = 3) := by
  have hb := (object_oh O).basic
  have hd := object_degIn_upper O
  rcases hO with h | h
  · refine ⟨O.lower, ?_, ?_, ?_⟩
    · rw [← h]; exact object_oh O
    · rw [← h]; exact hd.2
    · rw [← h]; exact hb.2.2.2.2.2.1
  · refine ⟨O.upper, ?_, ?_, ?_⟩
    · rw [← h]; exact (object_oh O).swap
    · intro hh; rw [← h, ← hb.2.2.2.2.1]; exact hd.2 hh
    · rw [← h, ← hb.2.2.2.2.1]; exact hb.2.2.2.2.2.1

/-- Src.Object Src.γL version: if either of two objects sharing a joint `c` and meeting only there is a
hyper-object, contradiction. -/
theorem object_one_joint_hyper_false (hM : M.IsMolecule) {P Q : Src.Object Src.γL M} {c : V}
    (hPc : P.upper = c ∨ P.lower = c) (hQc : Q.upper = c ∨ Q.lower = c)
    (hPQ : P.atoms ∩ Q.atoms = {c})
    (hhyp : (∃ R, P.shape = .hyper R) ∨ (∃ R, Q.shape = .hyper R)) : False := by
  obtain ⟨a, hA, hA3, hA2⟩ := object_oh_at P hPc
  obtain ⟨b, hB, hB3, hB2⟩ := object_oh_at Q hQc
  refine one_joint_hyper_false hM hA hB hPQ ?_
  rcases hhyp with h | h
  · have := hA3 h; omega
  · have := hB3 h; omega

end WaveTurbulence.GammaLow.FinalCount.H
