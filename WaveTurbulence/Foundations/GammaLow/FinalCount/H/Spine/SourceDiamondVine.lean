/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceDiamondVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceDiamondVine`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 An ordinary vine chain whose group contains a bond between its two joints is a single
vine of type I or V. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open Finset WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A chain which is an ordinary block and whose group has a joint-to-joint bond has a single
ingredient. -/
theorem chain_single_of_joint_bond {M : Molecule V D} (hM : M.IsMolecule) {S : Finset V}
    {a b : V} {n : ℕ} (hch : Src.Chain Src.γL M S a b n) (hB : M.IsBlock S a b) {z : D}
    (hza : M.atom z = a) (hzb : M.atom (M.mate z) = b) (hz : M.InGroup S z) :
    M.IsVineEnl S a b := by
  cases hch with
  | single h => exact Src.isSomeVine_γL_iff.mp h
  | @append S' T _ b' _ m hS hT hi hne =>
    have hX := hT
    exfalso
    have hP := chain_prefix_isBlock M hM hS hX hi hB
    have haS : a ∈ S' := hP.2.1
    have hbS : b ∉ S' := by
      intro hb
      have : b ∈ S' ∩ T := mem_inter.mpr ⟨hb, hX.block.2.2.1⟩
      rw [hi] at this
      exact hX.block.2.2.2.1 (mem_singleton.mp this).symm
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

end WaveTurbulence.GammaLow.FinalCount.H
