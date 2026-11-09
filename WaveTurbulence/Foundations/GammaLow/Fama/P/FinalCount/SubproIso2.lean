/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.SubproIso2` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.FinalCount.SubproIso
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.SubproIso2
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects


/-!
# SUBPRO (S4): transport of chains, VC's, DV's along an induced isomorphism
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount

variable {V D V' D' : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]
  [DecidableEq V'] [Fintype D'] [DecidableEq D']
theorem someVine_ends {M : Molecule V D} {T : Finset V} {b c : V} (h : Src.IsSomeVine γ M T b c) :
    b ∈ T ∧ c ∈ T ∧ b ≠ c := by
  have hX := h
  exact ⟨(Src.isBlock_of_isSomeVine hX).2.1, (Src.isBlock_of_isSomeVine hX).2.2.1, (Src.isBlock_of_isSomeVine hX).2.2.2.1⟩

variable {N : Molecule V D} {N' : Molecule V' D'} {B : Finset V} {B' : Finset V'} (I : InducedIso N N' B B')

theorem InducedIso.chain_map {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ N S a b n) (hS : S ⊆ B) :
    Src.Chain γ N' (S.image I.π) (I.π a) (I.π b) n := by
  induction h with
  | single hv => exact Src.Chain.single (by have hX := hv; exact isSomeVine_iso (I.restrict hS) hX)
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
    exact Src.Chain.append (ih hSB) (by have hX := hT; exact isSomeVine_iso (I.restrict hTB) hX) hint
      (fun h => hac (I.inj (hSB hae.1) (hTB hbc.2.1) h))

end WaveTurbulence.GammaLow.Fama
