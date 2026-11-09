/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceDiamondClosed
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceDiamondClosed`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Same-joints overlap of two ordinary blocks whose dart pairs are disjoint at both joints
would be a saturated component, contradicting `IsMolecule` (ii). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open Finset

set_option linter.unusedSectionVars false
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem inGroup_mate {M : Molecule V D} {S : Finset V} {x : D} (h : M.InGroup S x) :
    M.InGroup S (M.mate x) := ⟨h.2, by rw [M.mate_mate]; exact h.1⟩

/-- Two ordinary blocks with the same joints meeting exactly in the joints, with no shared
a-b bond dart, would form a saturated component; hence they share a joint-to-joint bond. -/
theorem diamond_shared_bond {M : Molecule V D} (hM : M.IsMolecule) {A B : Finset V}
    {a b : V} (hA : M.IsBlock A a b) (hB : M.IsBlock B a b) (hAB : A ∩ B = {a, b}) :
    ∃ z, M.atom z = a ∧ M.atom (M.mate z) = b ∧ M.InGroup A z ∧ M.InGroup B z := by
  by_contra H
  push Not at H
  have hAb := Mole.block_swap_joints M hA
  have hend : ∀ x, M.InGroup A x → M.InGroup B x → M.atom (M.mate x) = a ∨ M.atom (M.mate x) = b := by
    intro x h1 h2
    have : M.atom (M.mate x) ∈ A ∩ B := mem_inter.mpr ⟨h1.2, h2.2⟩
    rw [hAB] at this
    simpa using this
  refine diamond_disjoint_pairs_false hM hA hB ?_ ?_
  · rintro x hxa ⟨h1, h2⟩
    rcases hend x h1 h2 with h | h
    · exact block_joint_no_loop hA hxa h h1
    · exact H x hxa h h1 h2
  · rintro x hxb ⟨h1, h2⟩
    rcases hend x h1 h2 with h | h
    · have hm := hend (M.mate x) (inGroup_mate h1) (inGroup_mate h2)
      rw [M.mate_mate] at hm
      exact H (M.mate x) h (by rw [M.mate_mate]; exact hxb) (inGroup_mate h1) (inGroup_mate h2)
    · exact block_joint_no_loop hAb hxb h h1

end WaveTurbulence.GammaLow.FinalCount.H
