/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.PairSlots
public import WaveTurbulence.Foundations.RegStruct.PairSigns
public import WaveTurbulence.Foundations.RegStruct.PairLengths
public import WaveTurbulence.Foundations.RegStruct.DecodedLeaves
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.NodeCounts

/-! # Actual garden carriers for every drafted couple code

The finite endpoint argument constructs the specified pairing, rather than
assuming any of the unfinished source-regularity characterizations.
-/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree Finset

/-- The actual two-tree forest of a decoded couple. -/
def coupleForest (Q : RegCpl) : Fin 2 → TTree := ![Q.trees.1,Q.trees.2]

/-- Canonical global roots turn the two rooted leaf sets into the forest leaf set. -/
theorem coupleForest_leaf_iff (Q : RegCpl) (a : Fin 2 × Path) :
    a ∈ leafAddresses Q.trees.1 (0,[]) ∪ leafAddresses Q.trees.2 (1,[]) ↔
      a.2 ∈ (coupleForest Q a.1).leaves := by
  obtain ⟨j,p⟩ := a
  fin_cases j <;> simp [leafAddresses, addrExt, coupleForest]

/-- Every endpoint in the decoded pair list is an actual leaf of its actual tree. -/
theorem decodedCouple_pairs_valid (Q : RegCpl) :
    ∀ p ∈ Q.raw.2, p.1.2 ∈ (coupleForest Q p.1.1).leaves ∧
      p.2.2 ∈ (coupleForest Q p.2.1).leaves := by
  intro p hp
  constructor
  · apply (coupleForest_leaf_iff Q p.1).mp
    rw [couple_leafAddresses]
    exact (mem_pairEndpoints_iff _ _).mpr ⟨p,hp,Or.inl rfl⟩
  · apply (coupleForest_leaf_iff Q p.2).mp
    rw [couple_leafAddresses]
    exact (mem_pairEndpoints_iff _ _).mpr ⟨p,hp,Or.inr rfl⟩

/-- Every actual leaf occurs in the decoded pair list. -/
theorem decodedCouple_pairs_cover (Q : RegCpl) (ℓ : GLeaf (coupleForest Q)) :
    ℓ.1 ∈ pairEndpoints Q.raw.2 := by
  have h := (coupleForest_leaf_iff Q ℓ.1).mpr ℓ.2
  rw [couple_leafAddresses] at h
  exact h

/-- The pair slots have exactly the cardinality of the actual leaves. -/
theorem decodedCouple_pair_card (Q : RegCpl) :
    Q.raw.2.length * 2 = Fintype.card (GLeaf (coupleForest Q)) := by
  have hf : (∑ j, (coupleForest Q j).order) = Q.size := by
    simpa [coupleForest,Fin.sum_univ_two] using code_trees_order Q
  change (Q.pairsAt (0,[]) (1,[])).length * 2 = _
  rw [couple_pairsAt_length,Comb.card_gleaf,hf]
  omega

/-- The actual pair endpoints have the required source orientation. -/
theorem decodedCouple_pair_signs (Q : RegCpl) :
    ∀ p ∈ Q.raw.2, nodeSign ![1,-1] p.1 = 1 ∧ nodeSign ![1,-1] p.2 = -1 := by
  intro p hp
  exact couple_pairsAt_signs Q ![1,-1] (0,[]) (1,[])
    (by simp [nodeSign,pathSign]) (by simp [nodeSign,pathSign]) p hp

/-- The garden determined by the code's literal trees and literal leaf pairing. -/
noncomputable def decodedCouple (Q : RegCpl) : Garden 2 :=
  gardenOfPairs (coupleForest Q) ![1,-1] Q.raw.2 (decodedCouple_pairs_valid Q)
    (decodedCouple_pairs_cover Q) (decodedCouple_pair_card Q) (decodedCouple_pair_signs Q)

/-- Every code, even an unnormalized intermediate code, has its actual decoded carrier. -/
theorem decodedCouple_decodes (Q : RegCpl) : Q.Decodes (decodedCouple Q) := by
  refine ⟨⟨?_,rfl⟩,rfl,rfl,?_⟩
  · exact gardenOfPairs_plain _ _ _ _ _ _ _
  · intro ℓ
    exact gardenOfPairs_pair_mem _ _ _ _ _ _ _ ℓ

/-- The carrier's order is the code's order. -/
theorem decodedCouple_order (Q : RegCpl) : (decodedCouple Q).order = Q.size :=
  size_eq_order (decodedCouple_decodes Q)

end WaveTurbulence.Reg
