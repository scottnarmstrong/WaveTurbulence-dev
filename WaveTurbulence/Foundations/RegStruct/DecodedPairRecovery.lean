/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.EmbeddedCarrierUniqueness

/-! # Recovering every listed decoded pair from the actual carrier -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Matching a code gives equality with its literal indexed forest. -/
theorem decodes_forest {C : RegCpl} {G : Garden 2} (h : C.Decodes G) : G.tree = coupleForest C := by
  funext j
  fin_cases j
  · exact h.2.1
  · exact h.2.2.1

/-- The declared partner of every literal pair endpoint is its actual carrier partner. -/
theorem pair_of_decodes {C : RegCpl} {G : Garden 2} (h : C.Decodes G)
    (p : (Fin 2 × Path) × (Fin 2 × Path)) (hp : p ∈ symmPairs C.raw.2)
    (hv : p.1.2 ∈ (G.tree p.1.1).leaves) :
    (G.pair ⟨p.1,hv⟩).1 = p.2 :=
  decodedPair_functional C (h.2.2.2 ⟨p.1,hv⟩) hp

/-- Any two codes decoding the same actual carrier have exactly the same unordered pair relation. -/
theorem symmPairs_eq_of_decodes {C D : RegCpl} {G : Garden 2} (hC : C.Decodes G) (hD : D.Decodes G)
    (p : (Fin 2 × Path) × (Fin 2 × Path)) :
    p ∈ symmPairs C.raw.2 ↔ p ∈ symmPairs D.raw.2 := by
  have hforward : ∀ (C D : RegCpl), C.Decodes G → D.Decodes G →
      p ∈ symmPairs C.raw.2 → p ∈ symmPairs D.raw.2 := by
    intro C D hC hD hp
    have hv : p.1.2 ∈ (G.tree p.1.1).leaves := by
      rw [decodes_forest hC]
      rcases (mem_symmPairs_iff _ _).mp hp with hp | hp
      · exact (decodedCouple_pairs_valid C p hp).1
      · exact (decodedCouple_pairs_valid C p.swap hp).2
    have he := pair_of_decodes hC p hp hv
    have hrel := hD.2.2.2 (⟨p.1,hv⟩ : GLeaf G.tree)
    rw [he] at hrel
    exact hrel
  exact ⟨hforward C D hC hD,hforward D C hD hC⟩

/-- Equality of actual decoded carriers recovers their complete unordered pair relations. -/
theorem symmPairs_eq_of_carrier_eq {C D : RegCpl} (he : decodedCouple C = decodedCouple D)
    (p : (Fin 2 × Path) × (Fin 2 × Path)) :
    p ∈ symmPairs C.raw.2 ↔ p ∈ symmPairs D.raw.2 := by
  have hC := decodedCouple_decodes C
  rw [he] at hC
  exact symmPairs_eq_of_decodes hC (decodedCouple_decodes D) p

/-- Inclusion of literal pair blocks extends to their unordered pair relations. -/
theorem symmPairs_subset_of_pairs_subset {α : Type*} {P R : List (α × α)}
    (h : ∀ p ∈ P, p ∈ R) : ∀ p ∈ symmPairs P, p ∈ symmPairs R := by
  intro p hp
  rw [mem_symmPairs_iff] at hp ⊢
  exact hp.imp (fun hp => h p hp) (fun hp => h p.swap hp)

end WaveTurbulence.Reg
