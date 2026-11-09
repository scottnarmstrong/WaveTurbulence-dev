/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineChainConnected`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Connectivity of vine chains (TARGET defvine) -/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Both declared chain joints belong to its atom set. -/
theorem chain_joints_mem {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain Src.γL M S a b n) : a ∈ S ∧ b ∈ S := by
  induction h with
  | single h => have hX := h; exact ⟨hX.block.2.1,hX.block.2.2.1⟩
  | append _ hT _ _ ih =>
    have hX := hT
    exact ⟨mem_union_left _ ih.1,mem_union_right _ hX.block.2.2.1⟩

/-- Actual ordered concatenation preserves connectivity. -/
theorem chain_connected {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain Src.γL M S a b n) : GroupConnected M S := by
  induction h with
  | single h => have hX := h; exact (Src.IsSomeVine.vconnected hX)
  | append hS hT _ _ ih =>
    have hX := hT
    exact groupConnected_union M ih ((Src.IsSomeVine.vconnected hX)) (chain_joints_mem hS).2 hX.block.2.1

/-- TARGET defvine: every VC is connected. -/
theorem isVC_connected {M : Molecule V D} {S : Finset V} {a b : V}
    (h : Src.IsVC Src.γL M S a b) : GroupConnected M S := by
  obtain ⟨_hB,n,hn⟩ := h
  exact chain_connected hn

end WaveTurbulence.GammaLow.FinalCount.H
