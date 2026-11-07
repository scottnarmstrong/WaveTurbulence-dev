/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.SubproIso
public import WaveTurbulence.Foundations.Spine.SourceObjectUnion
import Mathlib.Tactic

/-!
# SUBPRO (S4): transport of chains, VC's, DV's along an induced isomorphism
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Stage1

variable {V D V' D' : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
  [DecidableEq V'] [Fintype D'] [DecidableEq D']
theorem someVine_ends {M : Molecule V D} {T : Finset V} {b c : V} (h : IsSomeVine M T b c) :
    b ∈ T ∧ c ∈ T ∧ b ≠ c := by
  obtain ⟨X, hX⟩ := h
  exact ⟨hX.1.2.1, hX.1.2.2.1, hX.1.2.2.2.1⟩

variable {N : Molecule V D} {N' : Molecule V' D'} {B : Finset V} {B' : Finset V'} (I : InducedIso N N' B B')

theorem InducedIso.chain_map {S : Finset V} {a b : V} {n : ℕ} (h : Chain N S a b n) (hS : S ⊆ B) :
    Chain N' (S.image I.π) (I.π a) (I.π b) n := by
  induction h with
  | single hv => exact Chain.single (by obtain ⟨X, hX⟩ := hv; exact ⟨X, (I.restrict hS).isVine hX⟩)
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
    exact Chain.append (ih hSB) (by obtain ⟨X, hX⟩ := hT; exact ⟨X, (I.restrict hTB).isVine hX⟩) hint
      (fun h => hac (I.inj (hSB hae.1) (hTB hbc.2.1) h))

end WaveTurbulence.RedSplice
