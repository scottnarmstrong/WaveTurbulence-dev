/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSplicePiece
import Mathlib.Tactic

/-!
# S2 REPRESENTS: audit of S2a's reading at TARGET L1956 (one gap entry per group, none per ladder)

TARGET L1950 and L1956 specify SG/LG/ZG "for each vine-like object in `𝒞`" (the atomic groups of
Lemma `vinechainlem`: HV, VC, HVC, DV), summarised in the factor `Z` (L1952, L1956); L1963 writes `Z` as a
product of `Z_v` over *some* atoms `v`, each a function of one opposite-direction pair of bonds at `v`.
Ladders inside a vine have gap `±r` or `0` (L1941), determined by the gap `r` of the vine, so they carry no
entry of their own.  `gapSpecification` (S2a) has exactly this shape:

* `gapSpecification_isSome_iff`: an atom of `G_sb` carries an entry iff it is the designated atom of a group;
* `gapSpecification_kind`: the entry at the designated atom of the group `S` has kind `σ S`;
* `gapSpecification_bijOn`: `S ↦ groupAtom S` is a bijection from the groups of `𝒞` onto the atoms with an entry.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
  WaveTurbulence.RedSplice

variable {w : ℕ} {G : Garden w}

/-- An atom of `G_sb` carries a gap entry iff it is the designated atom of a group of `𝒞`. -/
theorem gapSpecification_isSome_iff (hM : G.molecule.IsMolecule) (σ : Prescription G)
    (v : GBranch (stSt G σ).G.tree) :
    (gapSpecification G σ v).isSome ↔ ∃ S ∈ maximalGroups G.molecule, groupAtom G σ S = some v := by
  classical
  constructor
  · intro h
    by_contra hne
    unfold gapSpecification gapSpecificationMk at h
    rw [dite_eq_right_iff.mpr (fun h => absurd h hne)] at h
    simp at h
  · rintro ⟨S, hS, hv⟩
    obtain ⟨a, ha, e, he, -⟩ := gapSpecification_group hM σ hS
    have hat : groupAtom G σ S = some ((stSt G σ).M.pi (stSt G σ).hcls a) := by
      unfold groupAtom; rw [ha]; rfl
    rw [hat] at hv
    cases hv
    rw [he]; rfl

/-- The entry at the designated atom of a group has the kind prescribed for the group. -/
theorem gapSpecification_kind (hM : G.molecule.IsMolecule) (σ : Prescription G)
    {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    {v : GBranch (stSt G σ).G.tree} (hv : groupAtom G σ S = some v) :
    ∃ e, gapSpecification G σ v = some e ∧ e.kind = σ S := by
  obtain ⟨a, ha, e, he, hk, -⟩ := gapSpecification_group hM σ hS
  have hat : groupAtom G σ S = some ((stSt G σ).M.pi (stSt G σ).hcls a) := by
    unfold groupAtom; rw [ha]; rfl
  rw [hat] at hv
  cases hv
  exact ⟨e, he, hk⟩

/-- Every group of `𝒞` has a designated atom in `G_sb`. -/
theorem groupAtom_isSome (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroups G.molecule) : (groupAtom G σ S).isSome := by
  obtain ⟨a, ha⟩ := exists_groupJoint_eq hS
  unfold groupAtom; rw [ha]; rfl

/-- **One entry per group, none per ladder**: `S ↦ groupAtom S` is a bijection from the groups of `𝒞` onto the
atoms of `G_sb` that carry a gap entry; in particular the numbers agree. -/
theorem ncard_gapEntries (hM : G.molecule.IsMolecule) (σ : Prescription G) :
    Set.ncard {v : GBranch (stSt G σ).G.tree | (gapSpecification G σ v).isSome} =
      Set.ncard {S : Finset (GBranch G.tree) | S ∈ maximalGroups G.molecule} := by
  classical
  symm
  refine Set.ncard_congr (fun S hS => (groupAtom G σ S).get (groupAtom_isSome σ hS)) ?_ ?_ ?_
  · intro S hS
    exact (gapSpecification_isSome_iff hM σ _).mpr ⟨S, hS, by simp⟩
  · intro S S' hS hS' h
    exact groupAtom_inj hM σ hS hS' (v := (groupAtom G σ S).get (groupAtom_isSome σ hS))
      (Option.some_get _).symm (by rw [h]; exact (Option.some_get _).symm)
  · intro v hv
    obtain ⟨S, hS, hSv⟩ := (gapSpecification_isSome_iff hM σ v).mp hv
    exact ⟨S, hS, by simp [hSv]⟩

end WaveTurbulence.Represents
