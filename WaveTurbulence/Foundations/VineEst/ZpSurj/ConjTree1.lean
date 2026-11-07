/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Layers1
public import WaveTurbulence.Foundations.VineEst.ConjCoherent

/-! # ZP-SURJ: conjugation of embedded regular trees -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
open TTree WaveTurbulence.Reg WaveTurbulence.Links WaveTurbulence.LGSpine WaveTurbulence.ConjCoh WaveTurbulence.PL234

variable {w : ℕ} {LG LH : LayeredGarden w} {e : Fin w ≃ Fin w}

theorem chainEmb_conj (h : IsConjugateBy LG LH e) {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {t : TTree}
    (hE : ChainEmb LG.garden X ζ a t) : ChainEmb LH.garden (conjChain X) (-ζ) (phi e a) t where
  node := by
    show a.2 ∈ (LH.garden.tree (e a.1)).nodes
    rw [h.tree_eq]; exact hE.node
  tree := by
    show (LH.garden.tree (e a.1)).subtreeAt a.2 = (conjChain X).plug (-ζ) t
    rw [h.tree_eq, plug_conjChain]; exact hE.tree
  pairs := by
    intro p hp ℓ' hℓ'
    obtain ⟨q, hq, rfl⟩ := (mem_pairsAt_conjChain (addrCompat_phi e) X ζ a p).1 hp
    obtain ⟨ℓ0, rfl⟩ := (PL234.Conj.leafEquiv h).surjective ℓ'
    have h1 : q.1.2 ∈ (LG.garden.tree q.1.1).leaves := by
      have := hE.leaf_of_mem ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inl rfl⟩)
      exact this
    let ℓ1 : GLeaf LG.garden.tree := ⟨q.1, h1⟩
    have h2 := hE.pairs q hq ℓ1 rfl
    have hℓ0 : ℓ0.1 = q.2 := by
      have : (e ℓ0.1.1, ℓ0.1.2) = (e q.2.1, q.2.2) := hℓ'
      have e1 : e ℓ0.1.1 = e q.2.1 := (Prod.mk.inj this).1
      have e2 : ℓ0.1.2 = q.2.2 := (Prod.mk.inj this).2
      exact Prod.ext (e.injective e1) e2
    have h3 : LG.garden.pair ℓ1 = ℓ0 := Subtype.ext (h2.trans hℓ0.symm)
    have h4 : LG.garden.pair ℓ0 = ℓ1 := by rw [← h3, LG.garden.pair_pair]
    rw [PL234.Conj.pair_leaf, h4]
    rfl

theorem cohOn_chain_conj (h : IsConjugateBy LG LH e) (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path)
    (hc : CohOn LG (X.linksAt ζ a)) : CohOn LH ((conjChain X).linksAt (-ζ) (phi e a)) := by
  have hcnt := links_countP_conjChain (addrCompat_phi e)
    (fun x y => decide (layerAt LH x ≠ layerAt LH y)) (fun x y => by
      simp only [decide_eq_decide]; exact ne_comm) X ζ a
  have h0 : (List.countP (fun l => decide (layerAt LG (l.1) ≠ layerAt LG l.2)) (X.linksAt ζ a)) = 0 := by
    rw [List.countP_eq_zero]
    intro l hl
    simpa using hc l hl
  have h1 : (List.countP (fun l => decide (layerAt LH (phi e l.1) ≠ layerAt LH (phi e l.2)))
      (X.linksAt ζ a)) = 0 := by
    simpa [layerAt_conj h] using h0
  rw [h1] at hcnt
  intro l hl
  have := (List.countP_eq_zero.1 hcnt) l hl
  simpa using this

theorem decodesTree_conj {LG LH : LayeredGarden 1} (h : IsConjugateTree LG LH) {X : RegChain}
    (hX : X.DecodesTree LG.garden) : (conjChain X).DecodesTree LH.garden := by
  have hs : LH.garden.sig 0 = -LG.garden.sig 0 := h.sig_eq 0
  obtain ⟨h1, h2, h3⟩ := hX
  unfold RegChain.DecodesTree Garden.MatchesPairedTree
  rw [hs, lonePath_conjChain, plug_conjChain]
  refine ⟨(h.tree_eq 0).trans h1, ?_, ?_⟩
  · intro ℓ'
    obtain ⟨ℓ, rfl⟩ := (PL234.Conj.leafEquiv h).surjective ℓ'
    rw [PL234.Conj.mark_leaf, h2 ℓ]
    rfl
  · intro ℓ' hne
    obtain ⟨ℓ, rfl⟩ := (PL234.Conj.leafEquiv h).surjective ℓ'
    have hne' : ℓ.1.2 ≠ X.lonePath := hne
    have hp := h3 ℓ hne'
    rw [PL234.Conj.pair_leaf]
    have hmem := mem_pairsAt_conjChain (addrCompat_phi (Equiv.refl (Fin 1))) X (LG.garden.sig 0) (0, [])
    simp only [symmPairs, List.mem_append, List.mem_map] at hp ⊢
    rcases hp with hp | ⟨⟨q1, q2⟩, hq, hqe⟩
    · right
      refine ⟨(((Equiv.refl (Fin 1)) (LG.garden.pair ℓ).1.1, (LG.garden.pair ℓ).1.2),
        ((Equiv.refl (Fin 1)) ℓ.1.1, ℓ.1.2)), (hmem _).2 ⟨(ℓ.1, (LG.garden.pair ℓ).1), hp, rfl⟩, rfl⟩
    · left
      obtain ⟨e1, e2⟩ := Prod.mk.inj hqe
      refine (hmem _).2 ⟨(q1, q2), hq, ?_⟩
      simp only at e1 e2
      rw [e1, e2]
      rfl

theorem exists_conj_canon {p : ℕ} {H : LayeredGarden w} (hcan : IsCanonGC (p + 1) H) :
    ∃ e : Fin w ≃ Fin w, IsCanonGC (p + 1) (conjLayered H e) := by
  obtain ⟨hplain, hirr, hcrit⟩ := hcan
  rcases hirr with ⟨hw4, hI⟩ | ⟨hw2, hsig⟩
  · refine ⟨Equiv.refl (Fin w), ?_⟩
    have hconj := conjLayered_isConjugateBy H (Equiv.refl (Fin w))
    exact ⟨conj_isPlain hconj hplain, Or.inl ⟨hw4, conj_irreducible hconj hI⟩,
      conj_canonCriterion hconj hcrit⟩
  · subst hw2
    refine ⟨Equiv.swap (0 : Fin 2) 1, ?_⟩
    have hconj := conjLayered_isConjugateBy H (Equiv.swap (0 : Fin 2) 1)
    refine ⟨conj_isPlain hconj hplain, Or.inr ⟨rfl, fun j => ?_⟩, conj_canonCriterion hconj hcrit⟩
    show -H.garden.sig ((Equiv.swap (0 : Fin 2) 1).symm j) = (-1) ^ (j : ℕ)
    fin_cases j
    · simp [hsig]
    · simp [hsig]

/-- **Conjugate coherence of trees**: the tree analogue of `isCoherentCoupleAt_conj`. -/
theorem isCoherentTreeAt_conj {p q q' : ℕ} {X : RegChain} {LG LGbar : LayeredGarden 1}
    (h : IsConjugateTree LG LGbar) (hc : IsCoherentTreeAt p q q' X LG) :
    IsCoherentTreeAt p q q' (conjChain X) LGbar := by
  obtain ⟨hwf, hX, w', H, a, t, hcan, hemb, hsa, hcoh, hpa, hlone, hlay⟩ := hc
  obtain ⟨e, hcan'⟩ := exists_conj_canon hcan
  have hconj := conjLayered_isConjugateBy H e
  have hs : LGbar.garden.sig 0 = -LG.garden.sig 0 := h.sig_eq 0
  refine ⟨(wf_conjChain X).trans hwf, decodesTree_conj h hX, w', conjLayered H e, phi e a, t, hcan', ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [hs]; exact chainEmb_conj hconj hemb
  · rw [hs, nodeSign_conj hconj, hsa]
  · rw [hs]; exact cohOn_chain_conj hconj X _ a hcoh
  · exact (parAt_conj hconj p a).trans hpa
  · rw [lonePath_conjChain]
    show layerAt (conjLayered H e) (phi e (addrExt a X.lonePath)) = q'
    rw [layerAt_conj hconj]; exact hlone
  · intro z
    let z0 : GNode LG.garden.tree := ⟨z.1, by rw [← h.tree_eq z.1.1]; exact z.2⟩
    have h1 : LGbar.layer z = layerAt LG z0.1 := by
      rw [← layerAt_node LGbar z]
      exact layerAt_conj h z.1
    rw [h1, layerAt_node LG z0, hlay z0]
    show _ = layerAt (conjLayered H e) (phi e (addrExt a z.1.2))
    rw [layerAt_conj hconj]

end WaveTurbulence.ZpSurj
