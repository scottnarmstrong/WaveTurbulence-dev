/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Discharge
public import WaveTurbulence.Foundations.TVine.Struct.Cor116
public import WaveTurbulence.Foundations.TVine.Core.NoCutVertex
import Mathlib.Tactic

/-!
# N2 Theorem 1.15 (F1), (F2) at the molecule level (packet L3)

Unconditional (L1's proved N3 Lemma 6.2, N3 Lemma 4.1 and N2 Lemma 1.12):
* `connOn_groupGraph_iff`: connectivity of `A ⊆ S` inside the group graph of `S` is `M.GroupConnected A`;
* **`f1_mol`**: `S ∖ {j₁, j₂}` and `S ∖ {w}` (interior `w`) are connected;
* `subObjU_of_block`, `subObjU_of_hyperBlock`: a block / hyper-block `T ⊊ S` is an L1 sub-object;
* **`f2_mol`**: no block or hyper-block `T ⊊ S` contains a joint.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core

universe u v

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem connOn_groupGraph_iff (M : Molecule V D) {S A : Finset V} (hA : A ⊆ S) :
    ConnOn (groupGraph M S) A ↔ M.GroupConnected A := by
  rw [groupConnected_iff]
  have h : AdjIn (groupGraph M S) A = AdjIn (groupGraph M A) A := by
    funext a b
    exact propext ((adjIn_groupGraph_sub_iff M hA).trans (adjIn_groupGraph_iff M).symm)
  show ConnOn (groupGraph M S) A ↔ ConnOn (groupGraph M A) (groupGraph M A).verts
  rw [groupGraph_verts]
  unfold ConnOn
  rw [h]

/-- **N2 Theorem 1.15 (F1)** (DH23 `disjointlem` (i), (ii)). -/
theorem f1_mol {M : Molecule V D} {S : Finset V} {j₁ j₂ : V} (hT : M.IsTVine S j₁ j₂) :
    M.GroupConnected ((S.erase j₁).erase j₂) ∧
      ∀ w ∈ S, w ≠ j₁ → w ≠ j₂ → M.GroupConnected (S.erase w) := by
  have hTU := ((isTVine_iff M).mp hT).2
  refine ⟨?_, fun w hw h1 h2 => ?_⟩
  · have : ConnOn (groupGraph M S) ((S.erase j₁).erase j₂) :=
      interior_connOn (t6Ctx_of_isTVineU pendantPolesInput_holds hTU)
    rwa [connOn_groupGraph_iff M (fun x hx => (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2)] at this
  · have hwi : w ∈ Core.interior (groupGraph M S) j₁ j₂ :=
      Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, hw⟩⟩
    have := noCutVertex_holds (groupGraph M S) j₁ j₂ hTU w hwi
    rwa [groupGraph_verts, connOn_groupGraph_iff M (Finset.erase_subset _ _)] at this

/-- A block `T ⊊ S` is an L1 sub-object of the group graph of `S`. -/
theorem subObjU_of_block (M : Molecule V D) {S T : Finset V} {k₁ k₂ : V} (hTS : T ⊂ S)
    (hB : M.IsBlock T k₁ k₂) : IsSubObjU (groupGraph M S) ⟨T, k₁, k₂, false⟩ := by
  refine ⟨hTS, fun h => by simp at h, ?_⟩
  show IsBlockU (if false = true then _ else induce (groupGraph M S) T) k₁ k₂
  rw [if_neg (by decide), groupGraph_induce M hTS.subset]
  exact isBlockU_of_isBlock M hB

/-- A hyper-block `T ⊊ S` is an L1 sub-object of the group graph of `S`. -/
theorem subObjU_of_hyperBlock (M : Molecule V D) {S T : Finset V} {k₁ k₂ : V} (hTS : T ⊂ S)
    (hH : M.IsHyperBlock T k₁ k₂) : IsSubObjU (groupGraph M S) ⟨T, k₁, k₂, true⟩ := by
  obtain ⟨e, he, hB⟩ := hH
  have hk₁ : k₁ ∈ T := hB.2.1
  have hk₂ : k₂ ∈ T := hB.2.2.1
  have heT : M.InGroup T e := by
    have := he
    simp only [Molecule.ends, Sym2.eq_iff] at this
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by rw [h1]; exact hk₁, by rw [h2]; exact hk₂⟩
    · exact ⟨by rw [h1]; exact hk₂, by rw [h2]; exact hk₁⟩
  refine ⟨hTS, fun _ => ?_, ?_⟩
  · show (groupGraph M S).mult s(k₁, k₂) ≠ 0
    rw [← he]
    exact groupGraph_mult_ne_zero_of_dart M ⟨hTS.subset heT.1, hTS.subset heT.2⟩
  · show IsBlockU (if true = true then eraseBond (induce (groupGraph M S) T) s(k₁, k₂) else _) k₁ k₂
    rw [if_pos rfl, groupGraph_induce M hTS.subset, ← he, ← groupGraph_eraseBond M heT]
    exact isBlockU_of_isBlock _ hB

/-- **N2 Theorem 1.15 (F2)**: no proper block or hyper-block of a T-vine contains a joint. -/
theorem f2_mol {M : Molecule V D} {S : Finset V} {j₁ j₂ : V} (hT : M.IsTVine S j₁ j₂) :
    ∀ T ⊂ S, ∀ k₁ k₂ : V, (M.IsBlock T k₁ k₂ ∨ M.IsHyperBlock T k₁ k₂) → j₁ ∉ T ∧ j₂ ∉ T := by
  intro T hTS k₁ k₂ hBH
  have hTU := ((isTVine_iff M).mp hT).2
  have hU : ∃ h : Bool, IsSubObjU (groupGraph M S) ⟨T, k₁, k₂, h⟩ := by
    rcases hBH with hB | hH
    · exact ⟨false, subObjU_of_block M hTS hB⟩
    · exact ⟨true, subObjU_of_hyperBlock M hTS hH⟩
  obtain ⟨h, hU⟩ := hU
  exact containerJoints_holds (groupGraph M S) j₁ j₂ _ hTU.1 (loopless_of_isTVineU hTU)
    (interior_connOn (t6Ctx_of_isTVineU pendantPolesInput_holds hTU)) (noCutVertex_holds _ j₁ j₂ hTU) hU

end WaveTurbulence.TVine.Struct
