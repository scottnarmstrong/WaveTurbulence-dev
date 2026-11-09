/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineTwoJointSeparator
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineTwoJointSeparator`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Localizing an inner group when a shared outer joint is absent -/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Removing the second endpoint leaves a chain connected to its first endpoint. -/
theorem chain_erase_last_connected {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain Src.γL M S a b n) : GroupConnected M (S.erase b) := by
  have reach (u : V) (hu : u ∈ S.erase b) : (Mole.induced M (S.erase b)).SameComponent a u := by
    rcases chain_erase_endpoint_reach (z := b) h u hu with ⟨_hne,hp⟩ | ⟨hne,_hp⟩
    · exact hp
    · exact False.elim (hne rfl)
  intro u hu v hv
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (reach u hu)) (reach v hv)

/-- A VC remains connected when either specified joint is removed. -/
theorem isVC_erase_joint_connected {M : Molecule V D} {S : Finset V} {a b z : V}
    (h : Src.IsVC Src.γL M S a b) (hz : z=a ∨ z=b) : GroupConnected M (S.erase z) := by
  obtain ⟨_hB,n,hchain⟩ := h
  rcases hz with hz | hz
  · rw [hz]
    exact chain_erase_first_connected hchain
  · rw [hz]
    exact chain_erase_last_connected hchain

end WaveTurbulence.GammaLow.FinalCount.H
