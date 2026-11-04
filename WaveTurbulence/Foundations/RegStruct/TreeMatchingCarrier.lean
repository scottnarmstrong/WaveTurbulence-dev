/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CodeUniqueness

/-! # An actual paired tree determines its auxiliary couple carrier -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- The other index of a two-tree forest. -/
theorem fin_two_other {i s : Fin 2} (h : i ≠ s) : i = 1-s := by
  fin_cases i <;> fin_cases s <;> simp_all

/-- Every endpoint of an unordered raw pair is an actual leaf in the raw forest. -/
theorem symmPairs_valid (C : RegCpl) (p : (Fin 2 × Path) × (Fin 2 × Path))
    (hp : p ∈ symmPairs C.raw.2) :
    p.1.2 ∈ (C.raw.tree p.1.1).leaves ∧ p.2.2 ∈ (C.raw.tree p.2.1).leaves := by
  rw [raw_tree_eq_coupleForest]
  rcases (mem_symmPairs_iff _ _).mp hp with hp | hp
  · exact decodedCouple_pairs_valid C p hp
  · exact (decodedCouple_pairs_valid C p.swap hp).symm

/-- Unordered pair membership is invariant under exchanging the endpoints. -/
theorem symmPairs_swap_mem {α : Type*} (P : List (α × α)) (p : α × α)
    (hp : p ∈ symmPairs P) : p.swap ∈ symmPairs P := by
  rw [mem_symmPairs_iff] at hp ⊢
  exact hp.symm

/-- At each leaf on the nontrivial side, the actual tree matching identifies its auxiliary partner. -/
theorem tree_matching_pair_transfer (C D : RegCpl) (G : Garden 1)
    (hC : G.MatchesTreeCouple C.raw) (hD : G.MatchesTreeCouple D.raw)
    (p : (Fin 2 × Path) × (Fin 2 × Path)) (hp : p ∈ symmPairs C.raw.2)
    (hside : p.1.1 = (if G.sig 0 = 1 then 0 else 1)) : p ∈ symmPairs D.raw.2 := by
  let s : Fin 2 := if G.sig 0 = 1 then 0 else 1
  have hv := (symmPairs_valid C p hp).1
  change p.1.1 = s at hside
  have htree : C.raw.tree s = G.tree 0 := hC.1
  have hleaf : p.1.2 ∈ (G.tree 0).leaves := by
    rw [hside,htree] at hv
    exact hv
  let ℓ : GLeaf G.tree := ⟨(0,p.1.2),hleaf⟩
  have hc := hC.2.2 ℓ
  have hd := hD.2.2 ℓ
  change ((s,p.1.2),if G.IsLone ℓ then (1-s,[]) else (s,(G.pair ℓ).1.2)) ∈ symmPairs C.raw.2 at hc
  change ((s,p.1.2),if G.IsLone ℓ then (1-s,[]) else (s,(G.pair ℓ).1.2)) ∈ symmPairs D.raw.2 at hd
  have hex : p.1 = (s,p.1.2) := Prod.ext hside rfl
  rw [← hex] at hc hd
  have he := decodedPair_functional C hp hc
  rw [← he] at hd
  exact hd

/-- Two code auxiliary couples matched to the same actual tree have the same complete pair relation. -/
theorem tree_matching_symmPairs_transfer (C D : RegCpl) (G : Garden 1)
    (hC : G.MatchesTreeCouple C.raw) (hD : G.MatchesTreeCouple D.raw)
    (p : (Fin 2 × Path) × (Fin 2 × Path)) (hp : p ∈ symmPairs C.raw.2) : p ∈ symmPairs D.raw.2 := by
  let s : Fin 2 := if G.sig 0 = 1 then 0 else 1
  by_cases h0 : p.1.1 = s
  · exact tree_matching_pair_transfer C D G hC hD p hp h0
  by_cases h1 : p.2.1 = s
  · have hh := tree_matching_pair_transfer C D G hC hD p.swap (symmPairs_swap_mem _ _ hp) h1
    simpa only [Prod.swap_swap] using symmPairs_swap_mem _ _ hh
  · have hother : C.raw.tree (1-s) = .leaf := hC.2.1
    have hv := symmPairs_valid C p hp
    rw [fin_two_other h0,hother] at hv
    rw [fin_two_other h1,hother] at hv
    have he0 : p.1.2 = [] := Finset.mem_singleton.mp hv.1
    have he1 : p.2.2 = [] := Finset.mem_singleton.mp hv.2
    have he : p.1 = p.2 := Prod.ext ((fin_two_other h0).trans (fin_two_other h1).symm) (he0.trans he1.symm)
    have hf := decodedPair_no_fixed C p.1
    change (p.1,p.2) ∈ symmPairs C.raw.2 at hp
    rw [← he] at hp
    exact (hf hp).elim

/-- A tree's source matching relation determines its whole auxiliary couple carrier. -/
theorem decodedCouple_eq_of_matchingTree (C D : RegCpl) (G : Garden 1)
    (hC : G.MatchesTreeCouple C.raw) (hD : G.MatchesTreeCouple D.raw) : decodedCouple C = decodedCouple D := by
  let s : Fin 2 := if G.sig 0 = 1 then 0 else 1
  have ht : C.raw.tree = D.raw.tree := by
    funext j
    by_cases hj : j = s
    · rw [hj]
      exact hC.1.trans hD.1.symm
    · rw [fin_two_other hj]
      exact hC.2.1.trans hD.2.1.symm
  have hforest : (decodedCouple C).tree = (decodedCouple D).tree := by
    change coupleForest C = coupleForest D
    rw [← raw_tree_eq_coupleForest,← raw_tree_eq_coupleForest]
    exact ht
  apply carrier_eq_of_embedded_pairing D _ _ (decodedCouple_decodes C).1 (decodedCouple_decodes D).1
    hforest id Function.injective_id
  · intro ℓ
    exact tree_matching_symmPairs_transfer C D G hC hD _ ((decodedCouple_decodes C).2.2.2 ℓ)
  · exact (decodedCouple_decodes D).2.2.2

end WaveTurbulence.Reg
