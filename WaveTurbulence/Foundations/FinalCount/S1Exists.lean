/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.S1OverlapMain
public import WaveTurbulence.Foundations.FinalCount.S1Unique
public import WaveTurbulence.Foundations.Spine.SourceDoubleVinePartner
import Mathlib.Tactic

/-!
# Stage 1 combinatorics: existence in TARGET vinechainlem (L1930-L1933)

DH23 Lemma 8.1.  Let `Max` be the maximal vine-like atom sets.  Two distinct intersecting members
of `Max` are type-V vines with the same joints (`overlap_dichotomy`), and a third member of `Max`
meeting one of them is one of the two (partner uniqueness).  The collection `C` consists of the
members of `Max` meeting no other member, and the double vines `S ∪ T` of intersecting pairs.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Stage1
open Finset WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- The maximal vine-like atom sets. -/
@[expose] def maxVL (M : Molecule V D) : Set (Finset V) :=
  {S | IsVineLikeSet M S ∧ ∀ T, IsVineLikeSet M T → S ⊆ T → T = S}

/-- The collection of TARGET vinechainlem: isolated maximal vine-like sets, and the double vines
formed by two intersecting maximal vine-like sets. -/
@[expose] def stage1Collection (M : Molecule V D) : Set (Finset V) :=
  {X | (X ∈ maxVL M ∧ ∀ T ∈ maxVL M, T ≠ X → Disjoint X T) ∨
    ∃ S ∈ maxVL M, ∃ T ∈ maxVL M, S ≠ T ∧ ¬ Disjoint S T ∧ X = S ∪ T}

theorem ov (hM : M.IsMolecule) {S T : Finset V} (hS : S ∈ maxVL M) (hT : T ∈ maxVL M)
    (hne : S ≠ T) (hn : ¬ Disjoint S T) :
    ∃ a b, M.IsVine .V S a b ∧ M.IsVine .V T a b ∧ S ∩ T = {a, b} := by
  obtain ⟨P, hP⟩ := object_of_isVineLikeSet hS.1
  obtain ⟨Q, hQ⟩ := object_of_isVineLikeSet hT.1
  have hnST : ¬ S ⊆ T := fun h => hne (hS.2 T hT.1 h).symm
  have hnTS : ¬ T ⊆ S := fun h => hne (hT.2 S hS.1 h)
  have hnon : (P.atoms ∩ Q.atoms).Nonempty := by
    rw [hP, hQ]; exact Finset.not_disjoint_iff_nonempty_inter.mp hn
  rcases overlap_dichotomy hM hnon (by rwa [hP, hQ]) (by rwa [hP, hQ]) with ⟨W, hW⟩ | ⟨a, b, h1, h2, h3⟩
  · exfalso
    have hWvl := isVineLikeSet_of_object W
    have hSW : S ⊆ W.atoms := by rw [← hP]; exact subset_union_left.trans hW
    have hTW : T ⊆ W.atoms := by rw [← hQ]; exact subset_union_right.trans hW
    have hWS := hS.2 _ hWvl hSW
    exact hnTS (hWS ▸ hTW)
  · exact ⟨a, b, hP ▸ h1, hQ ▸ h2, by rw [← hP, ← hQ]; exact h3⟩

theorem partner (hM : M.IsMolecule) {S T U : Finset V} (hS : S ∈ maxVL M) (hT : T ∈ maxVL M)
    (hU : U ∈ maxVL M) (hne : S ≠ T) (hn : ¬ Disjoint S T) (hUS : ¬ Disjoint U S) :
    U = S ∨ U = T := by
  by_cases hUeq : U = S
  · exact Or.inl hUeq
  · right
    obtain ⟨a, b, hSa, hTa, hSTab⟩ := ov hM hS hT hne hn
    obtain ⟨c, e, hSc, hUc, hSUce⟩ := ov hM hS hU (Ne.symm hUeq) (fun h => hUS h.symm)
    exact (source_doubleVine_partner_unique_unordered M hM hSa hTa hSc hUc hSTab hSUce).symm

theorem pair_eq (hM : M.IsMolecule) {S T S' T' : Finset V} (hS : S ∈ maxVL M) (hT : T ∈ maxVL M)
    (hS' : S' ∈ maxVL M) (hT' : T' ∈ maxVL M) (hne : S ≠ T) (hn : ¬ Disjoint S T)
    (hne' : S' ≠ T') (hn' : ¬ Disjoint S' T') (hSS' : ¬ Disjoint S S') : S ∪ T = S' ∪ T' := by
  rcases partner hM hS hT hS' hne hn (fun h => hSS' h.symm) with h | h
  · subst h
    have hn'' : ¬ Disjoint T' S' := fun h => hn' h.symm
    rcases partner hM hS' hT hT' hne hn hn'' with h2 | h2
    · exact absurd h2.symm hne'
    · rw [h2]
  · subst h
    have hn'' : ¬ Disjoint T' S' := fun h => hn' h.symm
    rcases partner hM hS' hS hT' (Ne.symm hne) (fun h => hn h.symm) hn'' with h2 | h2
    · exact absurd h2.symm hne'
    · rw [h2, union_comm]

theorem stage1Collection_isGroup (hM : M.IsMolecule) {X : Finset V}
    (hX : X ∈ stage1Collection M) : IsStage1Group M X := by
  rcases hX with ⟨hX, _⟩ | ⟨S, hS, T, hT, hne, hn, rfl⟩
  · exact isStage1Group_of_vineLike hX.1
  · obtain ⟨a, b, h1, h2, h3⟩ := ov hM hS hT hne hn
    exact ⟨a, b, Or.inr (Or.inr (Or.inr ⟨S, T, h1, h2, h3, rfl⟩))⟩

theorem iso_pair_false (hM : M.IsMolecule) {X S' T' : Finset V} (hXi : ∀ T ∈ maxVL M, T ≠ X → Disjoint X T)
    (hS' : S' ∈ maxVL M) (hT' : T' ∈ maxVL M) (hne' : S' ≠ T') (hn' : ¬ Disjoint S' T') {z : V}
    (hzX : z ∈ X) (hz : z ∈ S' ∪ T') : False := by
  rcases mem_union.mp hz with h | h
  · by_cases hXS : S' = X
    · subst hXS
      exact hn' (hXi T' hT' (Ne.symm hne'))
    · exact Finset.disjoint_left.mp (hXi S' hS' hXS) hzX h
  · by_cases hXT : T' = X
    · subst hXT
      exact hn' (hXi S' hS' hne').symm
    · exact Finset.disjoint_left.mp (hXi T' hT' hXT) hzX h

theorem stage1Collection_disjoint (hM : M.IsMolecule) :
    (stage1Collection M).Pairwise (fun S T => Disjoint S T) := by
  intro X hX Y hY hXY
  by_contra hnd
  obtain ⟨z, hzX, hzY⟩ := Finset.not_disjoint_iff.mp hnd
  rcases hX with ⟨hXm, hXi⟩ | ⟨S, hS, T, hT, hne, hn, rfl⟩ <;>
    rcases hY with ⟨hYm, hYi⟩ | ⟨S', hS', T', hT', hne', hn', rfl⟩
  · exact Finset.disjoint_left.mp (hXi Y hYm (Ne.symm hXY)) hzX hzY
  · exact iso_pair_false hM hXi hS' hT' hne' hn' hzX hzY
  · exact iso_pair_false hM hYi hS hT hne hn hzY hzX
  · apply hXY
    rcases mem_union.mp hzX with h1 | h1 <;> rcases mem_union.mp hzY with h2 | h2
    · exact pair_eq hM hS hT hS' hT' hne hn hne' hn' (fun h => Finset.disjoint_left.mp h h1 h2)
    · exact (pair_eq hM hS hT hT' hS' hne hn (Ne.symm hne') (fun h => hn' h.symm)
        (fun h => Finset.disjoint_left.mp h h1 h2)).trans (union_comm _ _)
    · exact (union_comm _ _).trans (pair_eq hM hT hS hS' hT' (Ne.symm hne) (fun h => hn h.symm) hne' hn'
        (fun h => Finset.disjoint_left.mp h h1 h2))
    · exact (union_comm _ _).trans ((pair_eq hM hT hS hT' hS' (Ne.symm hne) (fun h => hn h.symm)
        (Ne.symm hne') (fun h => hn' h.symm) (fun h => Finset.disjoint_left.mp h h1 h2)).trans
        (union_comm _ _))

end WaveTurbulence.Stage1
