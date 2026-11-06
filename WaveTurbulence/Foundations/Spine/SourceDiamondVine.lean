/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceDiamondClosed
public import WaveTurbulence.Foundations.Spine.SourceVineSigma
public import WaveTurbulence.Foundations.Molecule.VineChainBlock
/-! An ordinary vine chain whose group contains a bond between its two joints is a single
vine of type I or V. -/
public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.LGSpine
open Finset WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem vine_typeIV_of_joint_bond {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (h : M.IsVine X S a b) {z : D} (hza : M.atom z = a) (hzb : M.atom (M.mate z) = b) :
    X = .I ∨ X = .V := by
  have hpos : 0 < M.bondsBetween a b := by
    unfold Molecule.bondsBetween Molecule.bonds
    apply Finset.card_pos.mpr
    by_cases hz : M.out z = true
    · exact ⟨z, by simp [hz, Molecule.ends, hza, hzb]⟩
    · refine ⟨M.mate z, ?_⟩
      have : M.out (M.mate z) = true := by
        rw [M.out_mate]; simpa using hz
      simp [this, Molecule.ends, M.mate_mate, hza, hzb, Sym2.eq_swap]
  have hs := isVine_bondsBetween h
  rw [hs] at hpos
  cases X <;> simp at hpos ⊢

/-- A chain which is an ordinary block and whose group has a joint-to-joint bond has a single
ingredient. -/
theorem chain_single_of_joint_bond {M : Molecule V D} (hM : M.IsMolecule) {S : Finset V}
    {a b : V} {n : ℕ} (hch : Vine.Chain M S a b n) (hB : M.IsBlock S a b) {z : D}
    (hza : M.atom z = a) (hzb : M.atom (M.mate z) = b) (hz : M.InGroup S z) :
    ∃ X, M.IsVine X S a b := by
  cases hch with
  | single h => exact h
  | @append S' T _ b' _ m hS hT hi hne =>
    obtain ⟨X, hX⟩ := hT
    exfalso
    have hP := Vine.chain_prefix_isBlock M hM hS hX hi hB
    have haS : a ∈ S' := hP.2.1
    have hbS : b ∉ S' := by
      intro hb
      have : b ∈ S' ∩ T := mem_inter.mpr ⟨hb, hX.1.2.2.1⟩
      rw [hi] at this
      exact hX.1.2.2.2.1 (mem_singleton.mp this).symm
    have h1 := (Mole.block_joint_degrees M hP).1
    have h2 := (Mole.block_joint_degrees M hB).1
    have hlt : M.degIn S' a < M.degIn (S' ∪ T) a := by
      unfold Molecule.degIn
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨z, ?_, ?_⟩
        · simp [Molecule.dartsAt, hza, hz]
        · simp only [mem_filter]
          rintro ⟨_, _, h⟩
          exact hbS (hzb ▸ h)
      · intro x hx
        simp only [mem_filter] at hx ⊢
        exact ⟨hx.1, mem_union_left _ hx.2.1, mem_union_left _ hx.2.2⟩
    omega

end WaveTurbulence.LGSpine
