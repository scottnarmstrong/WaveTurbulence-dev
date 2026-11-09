/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.SubproIso2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.S1Basic
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.RedSpliceInduced
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.SubproIso2`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# SUBPRO (S4): transport of chains, VC's, DV's along an induced isomorphism
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Stage1

variable {V D V' D' : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
  [DecidableEq V'] [Fintype D'] [DecidableEq D']
theorem someVine_ends {M : Molecule V D} {T : Finset V} {b c : V} (h : Src.IsSomeVine Src.γL M T b c) :
    b ∈ T ∧ c ∈ T ∧ b ≠ c := by
  have hX := h
  exact ⟨hX.block.2.1, hX.block.2.2.1, hX.block.2.2.2.1⟩

variable {N : Molecule V D} {N' : Molecule V' D'} {B : Finset V} {B' : Finset V'} (I : InducedIso N N' B B')

theorem InducedIso.chain_mapL {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain Src.γL N S a b n) (hS : S ⊆ B) :
    Src.Chain Src.γL N' (S.image I.π) (I.π a) (I.π b) n := by
  induction h with
  | single hv => exact Src.Chain.single (by have hX := hv; exact (I.restrict hS).isVineS hX)
  | @append S T a b c n hS' hT hST hac ih =>
    have hSB : S ⊆ B := fun v hv => hS (mem_union_left _ hv)
    have hTB : T ⊆ B := fun v hv => hS (mem_union_right _ hv)
    have hae := chain_ends hS'
    have hbc := someVine_ends hT
    have hint : (S.image I.π) ∩ (T.image I.π) = {I.π b} := by
      rw [← Finset.image_inter_of_injOn S T (I.inj.mono (by
        intro v hv
        rcases hv with hv | hv
        · exact hSB hv
        · exact hTB hv)), hST]
      simp
    rw [Finset.image_union]
    exact Src.Chain.append (ih hSB) (by have hX := hT; exact (I.restrict hTB).isVineS hX) hint
      (fun h => hac (I.inj (hSB hae.1) (hTB hbc.2.1) h))

alias _root_.WaveTurbulence.RedSplice.InducedIso.chain_mapL := _root_.WaveTurbulence.GammaLow.FinalCount.H.InducedIso.chain_mapL
end WaveTurbulence.GammaLow.FinalCount.H
