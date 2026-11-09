/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.ChainBlock
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceContainerAbsorb
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceDiamondContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceMaximalObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectFinite
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOneJointUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionEligible
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Base
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.VineDelObjects
public import WaveTurbulence.Foundations.Spine.SourceHyperDiamond
public import WaveTurbulence.Foundations.Spine.SourceDiamondContradiction
/-! Object-level hyper diamond: two selected vine-like objects with the same joints meeting
exactly in the joints, not nested, at least one of them a hyper-object: impossible. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SourceHyperDiamondObjects` (sha256 bb50030998c488b4344bd94c4c298b774c050b9f1448a2846900f0fc6b7e7e6c) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open Finset

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem object_oh (O : Object γv M) : OH M O.atoms O.upper O.lower := by
  rcases O with ⟨S, a, b, sh⟩
  cases sh with
  | vc h => exact Or.inl h.1
  | hyper R => exact Or.inr ⟨R.added, R.ends_eq, R.adjoint.1⟩

theorem object_degIn_upper (O : Object γv M) :
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

theorem object_diamond_false (hM : M.IsMolecule) {P Q : Object γv M}
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


/-- Mixed hyper/ordinary (or hyper/hyper) one-joint overlap: the shared joint would have
internal degree at least five. -/
theorem one_joint_hyper_false (hM : M.IsMolecule) {A B : Finset V} {a b c : V}
    (hA : OH M A c a) (hB : OH M B c b) (hAB : A ∩ B = {c})
    (hsum : 5 ≤ M.degIn A c + M.degIn B c) : False := by
  have hcA := hA.basic
  have hcB := hB.basic
  have hdis : ∀ x, M.atom x = c → ¬ (M.InGroup A x ∧ M.InGroup B x) := by
    rintro x hx ⟨h1, h2⟩
    have : M.atom (M.mate x) ∈ A ∩ B := mem_inter.mpr ⟨h1.2, h2.2⟩
    rw [hAB] at this
    exact hA.noloop hx (mem_singleton.mp this) h1
  have h1 := degIn_union_ge_add (M := M) A B c hdis
  have h2 := (Mole.degIn_le_deg M (A ∪ B) c).trans
    (Mole.deg_le_four M hM (hcA.1 hcA.2.1))
  omega

theorem object_oh_at (O : Object γv M) {c : V} (hO : O.upper = c ∨ O.lower = c) :
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

/-- Object γv version: if either of two objects sharing a joint `c` and meeting only there is a
hyper-object, contradiction. -/
theorem object_one_joint_hyper_false (hM : M.IsMolecule) {P Q : Object γv M} {c : V}
    (hPc : P.upper = c ∨ P.lower = c) (hQc : Q.upper = c ∨ Q.lower = c)
    (hPQ : P.atoms ∩ Q.atoms = {c})
    (hhyp : (∃ R, P.shape = .hyper R) ∨ (∃ R, Q.shape = .hyper R)) : False := by
  obtain ⟨a, hA, hA3, hA2⟩ := object_oh_at P hPc
  obtain ⟨b, hB, hB3, hB2⟩ := object_oh_at Q hQc
  refine one_joint_hyper_false hM hA hB hPQ ?_
  rcases hhyp with h | h
  · have := hA3 h; omega
  · have := hB3 h; omega

end WaveTurbulence.GammaLow.Famc
