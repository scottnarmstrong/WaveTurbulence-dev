/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PairMembership

/-! # Actual completely paired subcouples from literal included regular-code pair blocks -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem pairEndpoints_source_partner_mem {w : ℕ} (G : Garden w) (P : List (Pair w))
    (hP : ∀ p ∈ P, p ∈ sourcePairs G) (ℓ : GLeaf G.tree) (hℓ : ℓ.1 ∈ pairEndpoints P) :
    (G.pair ℓ).1 ∈ pairEndpoints P := by
  obtain ⟨p,hp,he⟩ := (mem_pairEndpoints_iff P ℓ.1).mp hℓ
  obtain ⟨x,y,hx,hy,hpair⟩ := sourcePairs_actual_endpoints G p (hP p hp)
  rcases he with he | he
  · have h : ℓ = x := Subtype.ext (he.trans hx.symm)
    rw [h,hpair]
    exact (mem_pairEndpoints_iff P y.1).mpr ⟨p,hp,Or.inr hy⟩
  · have h : ℓ = y := Subtype.ext (he.trans hy.symm)
    have hh : G.pair y = x := by rw [← hpair,G.pair_pair]
    rw [h,hh]
    exact (mem_pairEndpoints_iff P x.1).mpr ⟨p,hp,Or.inl hx⟩

/-- Genuine actual subtree extraction and the literal included code pairs supply the full
source embedded-subcouple criterion at arbitrary width. -/
theorem subCouple_of_source_block {w : ℕ} (C : RegCpl) (G : Garden w) (hG : G.IsPlain)
    (a b : GNode G.tree)
    (ha : Comb.subtree (G.tree a.1.1) a.1.2 = some C.trees.1)
    (hb : Comb.subtree (G.tree b.1.1) b.1.2 = some C.trees.2)
    (hP : ∀ p ∈ C.pairsAt a.1 b.1, p ∈ sourcePairs G) : Comb.IsSubCouple G a b := by
  have hcover (ℓ : GLeaf G.tree) :
      ℓ ∈ a.leavesBelow ∪ b.leavesBelow ↔ ℓ.1 ∈ pairEndpoints (C.pairsAt a.1 b.1) := by
    rw [← couple_leafAddresses C a.1 b.1]
    simp only [Finset.mem_union,leafAddresses_subtree_iff a _ ha ℓ,leafAddresses_subtree_iff b _ hb ℓ]
  intro ℓ hℓ
  exact ⟨Comb.pair_ne_of_plain hG ℓ,
    (hcover (G.pair ℓ)).mpr (pairEndpoints_source_partner_mem G _ hP ℓ ((hcover ℓ).mp hℓ))⟩

end WaveTurbulence.Reg.Skeleton
