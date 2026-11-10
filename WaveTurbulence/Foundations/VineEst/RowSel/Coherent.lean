/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RowSel.Basic
public import WaveTurbulence.Foundations.Spine.CoherentObjects
public import WaveTurbulence.Foundations.Spine.PL234Draft.ChainFacts
public import WaveTurbulence.Foundations.VineEst.ConjCoherent
public import WaveTurbulence.Foundations.VineEst.CodeConjPairs
public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4KConj
public import WaveTurbulence.Foundations.WaveB.Lemmas

/-! # V5W-B (ruling F2), B2: coherent objects have incoherency index `0`, so the selector is plain on them

* `incoherency_eq_zero_of_isCoherentCoupleAt`: `IsCoherentCoupleAt p q q' Q LG → LG.incoherency Q.links = 0`.  The
  embedding in the canonical garden `H` carries `CohOn H (Q.linksAt a b)` and the layer identity
  `LG.layer z = layerAt H (addrExt (root of z) z.path)`; the links of `Q` at the roots `(0, [])`, `(1, [])` are carried to
  `Q.linksAt a b` by the address translation (`PL234.couple_linksAt_map`).
* `incoherency_eq_zero_of_isCoherentTreeAt`: the same for trees (`PL234.chain_linksAt_map`).
* `incoherency_eq_zero_of_isCoherentCoupleAt_conj`, `incoherency_eq_zero_of_isCoherentTreeAt_conj`: the conjugate
  orientation — a coherent conjugate couple (tree) has a coherent native couple (tree): the incoherency index is
  invariant under conjugation (`ConjCoh.incoherency_conj`, `tree_incoherency_conj`).
* `KQsel_of_isCoherentCoupleAt`, …: hence the selected kernels are `KQstar`/`KTstar` on coherent objects, for every
  selector.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.VineEst
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.ConjCoh TTree

/-- **Bridge, couples**: an embedded coherent couple has incoherency index `0`. -/
theorem incoherency_eq_zero_of_isCoherentCoupleAt {p q q' : ℕ} {Q : RegCpl} {LG : LayeredGarden 2}
    (h : IsCoherentCoupleAt p q q' Q LG) : LG.incoherency Q.links = 0 := by
  obtain ⟨_, hQ, w, H, a, b, _, _, _, _, hcoh, _, _, hlay⟩ := h
  rw [coherent_iff hQ]
  intro l hl
  let f : Fin 2 × Path → Fin w × Path := fun z => addrExt (if z.1 = 0 then a else b) z.2
  have hf : ∀ x r, f (addrExt x r) = addrExt (f x) r := by
    intro x r
    simp only [f, addrExt, List.append_assoc]
  have hm := PL234.couple_linksAt_map Q f hf (0, []) (1, [])
  have h0 : f (0, []) = a := by simp [f, addrExt]
  have h1 : f (1, []) = b := by simp [f, addrExt]
  rw [h0, h1] at hm
  have hl' : (f l.1, f l.2) ∈ Q.linksAt a b := by
    rw [hm]
    exact List.mem_map.mpr ⟨l, hl, rfl⟩
  have hc := hcoh _ hl'
  obtain ⟨hb1, hb2, _⟩ := link_branching hQ hl
  have e : ∀ (x : Fin 2 × Path) (hx : x.2 ∈ (LG.garden.tree x.1).nodes), layerAt LG x = layerAt H (f x) :=
    fun x hx => (layerAt_node LG ⟨x, hx⟩).trans (hlay ⟨x, hx⟩)
  exact (e l.1 (TTree.branching_subset_nodes _ hb1)).trans
    (hc.trans (e l.2 (TTree.branching_subset_nodes _ hb2)).symm)

/-- **Bridge, trees**: an embedded coherent tree has incoherency index `0`. -/
theorem incoherency_eq_zero_of_isCoherentTreeAt {p q q' : ℕ} {X : RegChain} {LG : LayeredGarden 1}
    (h : IsCoherentTreeAt p q q' X LG) : LG.incoherency (X.treeLinks (LG.garden.sig 0)) = 0 := by
  obtain ⟨_, hX, w, H, a, t, _, _, _, hcoh, _, _, hlay⟩ := h
  rw [tree_coherent_iff hX]
  intro l hl
  let f : Fin 1 × Path → Fin w × Path := fun z => addrExt a z.2
  have hf : ∀ x r, f (addrExt x r) = addrExt (f x) r := by
    intro x r
    simp only [f, addrExt, List.append_assoc]
  have hm := PL234.chain_linksAt_map X f hf (LG.garden.sig 0) (0, [])
  have h0 : f (0, []) = a := by simp [f, addrExt]
  rw [h0] at hm
  have hl' : (f l.1, f l.2) ∈ X.linksAt (LG.garden.sig 0) a := by
    rw [hm]
    exact List.mem_map.mpr ⟨l, hl, rfl⟩
  have hc := hcoh _ hl'
  have hb1 := (tree_mem_pairEndpoints_links_iff hX _).1 ((mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inl rfl⟩)
  have hb2 := (tree_mem_pairEndpoints_links_iff hX _).1 ((mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inr rfl⟩)
  have e : ∀ (x : Fin 1 × Path) (hx : x.2 ∈ (LG.garden.tree x.1).nodes), layerAt LG x = layerAt H (f x) :=
    fun x hx => (layerAt_node LG ⟨x, hx⟩).trans (hlay ⟨x, hx⟩)
  exact (e l.1 (TTree.branching_subset_nodes _ hb1)).trans
    (hc.trans (e l.2 (TTree.branching_subset_nodes _ hb2)).symm)

section ConjTree
open WaveTurbulence.ConjCoh WaveTurbulence.PL234

/-- `ZpSurj.decodesTree_conj` (ZpSurj/ConjTree1), restated here: that module lies above the bundle modules that
use the bridges. -/
theorem decodesTree_conj_rowSel {LG LH : LayeredGarden 1} (h : IsConjugateTree LG LH) {X : RegChain}
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

end ConjTree

/-- **The incoherency index of a conjugate tree** equals that of the tree. -/
theorem tree_incoherency_conj {LG LGbar : LayeredGarden 1} (h : IsConjugateTree LG LGbar) {X : RegChain}
    (hX : X.DecodesTree LG.garden) :
    LGbar.incoherency ((conjChain X).treeLinks (LGbar.garden.sig 0)) = LG.incoherency (X.treeLinks (LG.garden.sig 0)) := by
  have hX' := decodesTree_conj_rowSel h hX
  rw [tree_incoherency_eq_count hX', tree_incoherency_eq_count hX]
  have hs : LGbar.garden.sig 0 = -LG.garden.sig 0 := h.sig_eq 0
  have hcnt := links_countP_conjChain (addrCompat_phi (Equiv.refl (Fin 1)))
    (fun x y => decide (layerAt LGbar x ≠ layerAt LGbar y)) (fun x y => by
      simp only [decide_eq_decide]; exact ne_comm) X (LG.garden.sig 0) (0, [])
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  unfold RegChain.treeLinks
  rw [hs]
  have hphi : phi (Equiv.refl (Fin 1)) ((0 : Fin 1), ([] : Path)) = (0, []) := rfl
  rw [hphi] at hcnt
  rw [hcnt]
  refine List.countP_congr fun l _ => ?_
  simp [ConjCoh.layerAt_conj h]

/-- **Bridge, conjugate couples**: if the conjugate (along the root swap) of a layered couple is coherent with code
`conjCpl Q`, the couple has incoherency index `0` for `Q`. -/
theorem incoherency_eq_zero_of_isCoherentCoupleAt_conj {p q q' : ℕ} {Q : RegCpl} {LG : LayeredGarden 2}
    (hQ : Q.Decodes LG.garden)
    (h : IsCoherentCoupleAt p q q' (conjCpl Q) (conjLayered LG (Equiv.swap (0 : Fin 2) 1))) :
    LG.incoherency Q.links = 0 := by
  rw [← ConjCoh.incoherency_conj (ConjCoh.conjLayered_isConjugateCouple LG) hQ]
  exact incoherency_eq_zero_of_isCoherentCoupleAt h

/-- **Bridge, conjugate trees**: if the conjugate of a layered tree is coherent with code `conjChain X`, the tree has
incoherency index `0` for `X`. -/
theorem incoherency_eq_zero_of_isCoherentTreeAt_conj {p q q' : ℕ} {X : RegChain} {LG : LayeredGarden 1}
    (hX : X.DecodesTree LG.garden)
    (h : IsCoherentTreeAt p q q' (conjChain X) (conjLayered LG (Equiv.refl (Fin 1)))) :
    LG.incoherency (X.treeLinks (LG.garden.sig 0)) = 0 := by
  rw [← tree_incoherency_conj (conjLayered_isConjugateBy LG (Equiv.refl (Fin 1))) hX]
  exact incoherency_eq_zero_of_isCoherentTreeAt h

section Selector
variable {u : Unit} [S : RowSel u] {d : ℕ}

end Selector

end WaveTurbulence.VineEst
