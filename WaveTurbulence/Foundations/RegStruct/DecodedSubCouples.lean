/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.SourceTreeCount
public import WaveTurbulence.Foundations.RegStruct.CrossingSupport

/-! # Actual completely paired sub-couples from decoded pair blocks -/

public section
namespace WaveTurbulence.Reg
open TTree Finset

/-- At an actual rooted subtree, the local leaf addresses are precisely the leaves below its root. -/
theorem leafAddresses_subtree_iff {w : ℕ} {tree : Fin w → TTree} (a : GNode tree)
    (u : TTree) (hu : Comb.subtree (tree a.1.1) a.1.2 = some u) (ℓ : GLeaf tree) :
    ℓ.1 ∈ leafAddresses u a.1 ↔ ℓ ∈ a.leavesBelow := by
  rw [GNode.leavesBelow,Finset.mem_filter]
  simp only [Finset.mem_univ,true_and,GNode.IsDesc]
  constructor
  · intro h
    obtain ⟨p,_,he⟩ := Finset.mem_image.mp h
    have hj := congrArg (fun z : Fin w × Path => z.1) he
    have hp := congrArg (fun z : Fin w × Path => z.2) he
    exact ⟨hj,⟨p,hp⟩⟩
  · rintro ⟨hj,p,hp⟩
    apply Finset.mem_image.mpr
    have hv : a.1.2 ++ p ∈ (tree a.1.1).leaves := by
      rw [hp,hj]
      exact ℓ.2
    exact ⟨p,(Comb.subtree_leaves_iff hu p).mpr hv,Prod.ext hj hp⟩

/-- A literal pair block is closed under the ambient decoded pairing. -/
theorem pairEndpoints_partner_mem (Q : RegCpl) (G : Garden 2) (hG : Q.Decodes G)
    (P : List ((Fin 2 × Path) × (Fin 2 × Path))) (hP : ∀ p ∈ P, p ∈ Q.raw.2)
    (ℓ : GLeaf G.tree) (hℓ : ℓ.1 ∈ pairEndpoints P) : (G.pair ℓ).1 ∈ pairEndpoints P := by
  obtain ⟨p,hp,he⟩ := (mem_pairEndpoints_iff P ℓ.1).mp hℓ
  have hactual := hG.2.2.2 ℓ
  rcases he with he | he
  · have hc : (ℓ.1,p.2) ∈ symmPairs Q.raw.2 := by
      rw [he]
      exact (mem_symmPairs_iff _ _).mpr (Or.inl (hP p hp))
    rw [decodedPair_functional Q hactual hc]
    exact (mem_pairEndpoints_iff P p.2).mpr ⟨p,hp,Or.inr rfl⟩
  · have hc : (ℓ.1,p.1) ∈ symmPairs Q.raw.2 := by
      rw [he]
      exact (mem_symmPairs_iff _ _).mpr (Or.inr (hP p hp))
    rw [decodedPair_functional Q hactual hc]
    exact (mem_pairEndpoints_iff P p.1).mpr ⟨p,hp,Or.inl rfl⟩

/-- Actual extraction and a literal included code-pair block produce a genuine sub-couple.
This helper is a finite-pairing statement; each structural use must supply the
extraction equations and the actual inclusion from its constructor. -/
theorem subCouple_of_decoded_block (Q C : RegCpl) (G : Garden 2) (hG : Q.Decodes G)
    (a b : GNode G.tree)
    (ha : Comb.subtree (G.tree a.1.1) a.1.2 = some C.trees.1)
    (hb : Comb.subtree (G.tree b.1.1) b.1.2 = some C.trees.2)
    (hP : ∀ p ∈ C.pairsAt a.1 b.1, p ∈ Q.raw.2) : Comb.IsSubCouple G a b := by
  have hcover : ∀ ℓ : GLeaf G.tree,
      ℓ ∈ a.leavesBelow ∪ b.leavesBelow ↔ ℓ.1 ∈ pairEndpoints (C.pairsAt a.1 b.1) := by
    intro ℓ
    rw [← couple_leafAddresses C a.1 b.1]
    simp only [Finset.mem_union,leafAddresses_subtree_iff a _ ha ℓ,leafAddresses_subtree_iff b _ hb ℓ]
  intro ℓ hℓ
  constructor
  · intro he
    have hm := (G.pair_eq_iff ℓ).mp he
    exact hm (hG.1.1 ℓ)
  · exact (hcover (G.pair ℓ)).mpr
      (pairEndpoints_partner_mem Q G hG _ hP ℓ ((hcover ℓ).mp hℓ))

end WaveTurbulence.Reg
