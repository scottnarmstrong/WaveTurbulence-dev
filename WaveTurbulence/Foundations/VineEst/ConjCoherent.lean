/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ConjEmbed

/-!
# Conjugate coherence (CONJ-COH; TARGET Def `defcoh`, Prop `deflink`, L899)

* `decodes_conj`: if `Q` decodes the couple carrier `LG.garden` and `LGbar` is its conjugate
  (`IsConjugateCouple LG LGbar`: swapped trees, opposite signs, same layers), then `conjCpl Q` decodes `LGbar.garden`.
* `isCoherentCoupleAt_conj`: if `Q` is a coherent couple at `(p, q, q')` in `LG`, then `conjCpl Q` is a coherent
  couple at `(p, q', q)` in `LGbar`.  The proof conjugates the embedding garden `H` (along the identity for width
  `≥ 4`, along the swap of the two roots for width `2`), transporting the canonical criterion, the embedding, the
  links and the layers.
* `incoherency_conj`: the incoherency index of `conjCpl Q` in `LGbar` equals that of `Q` in `LG`.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.ConjCoh

open WaveTurbulence TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.Links WaveTurbulence.Reg

variable {LG LGbar : LayeredGarden 2}

theorem phi_swap_one : phi (Equiv.swap (0 : Fin 2) 1) ((1 : Fin 2), ([] : Path)) = ((0 : Fin 2), ([] : Path)) := by
  simp [phi]

theorem phi_swap_zero : phi (Equiv.swap (0 : Fin 2) 1) ((0 : Fin 2), ([] : Path)) = ((1 : Fin 2), ([] : Path)) := by
  simp [phi]

/-- The conjugate code decodes the conjugate carrier. -/
theorem decodes_conj (h : IsConjugateCouple LG LGbar) {Q : RegCpl} (hQ : Q.Decodes LG.garden) :
    (conjCpl Q).Decodes LGbar.garden := by
  obtain ⟨hC, ht0, ht1, hpairs⟩ := hQ
  have hsig := hC.2
  refine ⟨⟨conj_isPlain h hC.1, ?_⟩, ?_, ?_, ?_⟩
  · funext j
    fin_cases j
    · have := h.sig_eq 1
      simp only [Equiv.swap_apply_right] at this
      simp [this, hsig]
    · have := h.sig_eq 0
      simp only [Equiv.swap_apply_left] at this
      simp [this, hsig]
  · have := h.tree_eq 1
    simp only [Equiv.swap_apply_right] at this
    rw [trees_conjCpl]; exact this.trans ht1
  · have := h.tree_eq 0
    simp only [Equiv.swap_apply_left] at this
    rw [trees_conjCpl]; exact this.trans ht0
  · intro ℓ'
    obtain ⟨ℓ, rfl⟩ := (PL234.Conj.leafEquiv h).surjective ℓ'
    have hp := hpairs ℓ
    rw [PL234.Conj.pair_leaf]
    have hmem := mem_pairsAt_conjCpl (addrCompat_phi (Equiv.swap (0 : Fin 2) 1)) Q (0, []) (1, [])
    rw [phi_swap_one, phi_swap_zero] at hmem
    simp only [RegCpl.raw, symmPairs, List.mem_append, List.mem_map] at hp ⊢
    rcases hp with hp | ⟨⟨q1, q2⟩, hq, hqe⟩
    · right
      exact ⟨(phi (Equiv.swap (0 : Fin 2) 1) (LG.garden.pair ℓ).1,
        phi (Equiv.swap (0 : Fin 2) 1) ℓ.1), (hmem _).2 ⟨(ℓ.1, (LG.garden.pair ℓ).1), hp, rfl⟩, rfl⟩
    · left
      obtain ⟨e1, e2⟩ := Prod.mk.inj hqe
      refine (hmem _).2 ⟨(q1, q2), hq, ?_⟩
      show (phi (Equiv.swap (0 : Fin 2) 1) ℓ.1, phi (Equiv.swap (0 : Fin 2) 1) (LG.garden.pair ℓ).1) = _
      rw [← e1, ← e2]


theorem isCoherentCoupleAt_conj_aux {p q q' : ℕ} {Q : RegCpl} (h : IsConjugateCouple LG LGbar)
    (hwf : Q.wf = true) (hQ : Q.Decodes LG.garden) {w : ℕ} (H : LayeredGarden w) (a b : Fin w × Path)
    (e : Fin w ≃ Fin w) (hcan' : IsCanonGC (p + 1) (conjLayered H e))
    (hemb : Embeds H.garden Q a b) (hsb : nodeSign H.garden.sig b = -1) (hsa : nodeSign H.garden.sig a = 1)
    (hcoh : CohOn H (Q.linksAt a b)) (hpa : parAt H p a = q) (hpb : parAt H p b = q')
    (hlay : ∀ z : GNode LG.garden.tree,
      LG.layer z = layerAt H (addrExt (if z.1.1 = 0 then a else b) z.1.2)) :
    IsCoherentCoupleAt p q' q (conjCpl Q) LGbar := by
  have hconj := conjLayered_isConjugateBy H e
  refine ⟨(wf_conjCpl Q).trans hwf, decodes_conj h hQ, w, conjLayered H e, phi e b, phi e a, hcan',
    embeds_conj hconj hemb, ?_, ?_, cohOn_conj hconj Q a b hcoh, (parAt_conj hconj p b).trans hpb,
    (parAt_conj hconj p a).trans hpa, ?_⟩
  · rw [nodeSign_conj hconj, hsb]; rfl
  · rw [nodeSign_conj hconj, hsa]
  · intro z
    obtain ⟨z0, rfl⟩ := (PL234.Conj.nodeEquiv h).surjective z
    rw [PL234.Conj.layer_node h, hlay z0]
    have hz : (PL234.Conj.nodeEquiv h z0).1.1 = Equiv.swap (0 : Fin 2) 1 z0.1.1 := rfl
    have hz2 : (PL234.Conj.nodeEquiv h z0).1.2 = z0.1.2 := rfl
    rw [hz2, ← layerAt_conj hconj]
    rcases Fin.exists_fin_two.1 ⟨z0.1.1, rfl⟩ with h0 | h0
    · rw [h0] at hz ⊢
      simp only [Equiv.swap_apply_left] at hz
      simp [hz, phi, addrExt]
    · rw [h0] at hz ⊢
      simp only [Equiv.swap_apply_right] at hz
      simp [hz, phi, addrExt]


/-- **Conjugate coherence** (TARGET Def `defcoh`, L899).  If `Q` is a coherent couple at `(p, q, q')` in `LG`
and `LGbar` is the conjugate of `LG` (`IsConjugateCouple`: swapped trees, opposite signs, same layers), then the
conjugate code `conjCpl Q` is a coherent couple at `(p, q', q)` in `LGbar`. -/
theorem isCoherentCoupleAt_conj {p q q' : ℕ} {Q : RegCpl} (h : IsConjugateCouple LG LGbar)
    (hc : IsCoherentCoupleAt p q q' Q LG) : IsCoherentCoupleAt p q' q (conjCpl Q) LGbar := by
  obtain ⟨hwf, hQ, w, H, a, b, hcan, hemb, hsa, hsb, hcoh, hpa, hpb, hlay⟩ := hc
  obtain ⟨hplain, hirr, hcrit⟩ := hcan
  rcases hirr with ⟨hw4, hI⟩ | ⟨hw2, hsig⟩
  · refine isCoherentCoupleAt_conj_aux h hwf hQ H a b (Equiv.refl (Fin w)) ?_ hemb hsb hsa hcoh hpa hpb hlay
    have hconj := conjLayered_isConjugateBy H (Equiv.refl (Fin w))
    exact ⟨conj_isPlain hconj hplain, Or.inl ⟨hw4, conj_irreducible hconj hI⟩,
      conj_canonCriterion hconj hcrit⟩
  · subst hw2
    refine isCoherentCoupleAt_conj_aux h hwf hQ H a b (Equiv.swap (0 : Fin 2) 1) ?_ hemb hsb hsa hcoh hpa
      hpb hlay
    have hconj := conjLayered_isConjugateBy H (Equiv.swap (0 : Fin 2) 1)
    refine ⟨conj_isPlain hconj hplain, Or.inr ⟨rfl, fun j => ?_⟩, conj_canonCriterion hconj hcrit⟩
    show -H.garden.sig ((Equiv.swap (0 : Fin 2) 1).symm j) = (-1) ^ (j : ℕ)
    fin_cases j
    · simp [hsig]
    · simp [hsig]

/-- The incoherency index of the conjugate couple equals that of the couple. -/
theorem incoherency_conj (h : IsConjugateCouple LG LGbar) {Q : RegCpl} (hQ : Q.Decodes LG.garden) :
    LGbar.incoherency (conjCpl Q).links = LG.incoherency Q.links := by
  have hQ' := decodes_conj h hQ
  rw [incoherency_eq_count hQ', incoherency_eq_count hQ]
  have hcnt := links_countP_conjCpl (addrCompat_phi (Equiv.swap (0 : Fin 2) 1))
    (fun x y => decide (layerAt LGbar x ≠ layerAt LGbar y)) (fun x y => by
      simp only [decide_eq_decide]; exact ne_comm) Q (0, []) (1, [])
  rw [phi_swap_one, phi_swap_zero] at hcnt
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  unfold RegCpl.links
  rw [hcnt]
  refine List.countP_congr fun l _ => ?_
  simp [layerAt_conj h]


/-- A conjugate of every layered couple exists (along the swap of the two roots). -/
theorem conjLayered_isConjugateCouple (LG : LayeredGarden 2) :
    IsConjugateCouple LG (conjLayered LG (Equiv.swap (0 : Fin 2) 1)) :=
  conjLayered_isConjugateBy LG _

end WaveTurbulence.ConjCoh
