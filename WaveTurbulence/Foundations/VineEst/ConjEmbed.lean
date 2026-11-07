/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ConjCanon
public import WaveTurbulence.Foundations.VineEst.CodeConjPairs
public import WaveTurbulence.Foundations.Spine.CoherentObjects

/-!
# Transport of embeddings, layers and parent layers along a conjugation (CONJ-COH)

For `h : IsConjugateBy LG LH e` and the address map `φ x = (e x.1, x.2)`:
* `embeds_conj`: an embedded couple `Q` at `(a, b)` in `LG.garden` gives the embedded conjugate code at
  `(φ b, φ a)` in `LH.garden` (TARGET Def `subobject`);
* `layerAt_conj`, `parAt_conj`: the layer and the parent layer at `φ x` in `LH` equal those at `x` in `LG`;
* `nodeSign_conj`: root signs reverse;
* `cohOn_conj`: coherence of the links is preserved.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.ConjCoh

open WaveTurbulence TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.Links WaveTurbulence.Reg

variable {w : ℕ} {LG LH : LayeredGarden w} {e : Fin w ≃ Fin w}

/-- Relabel the root index of an address by `e`. -/
def phi (e : Fin w ≃ Fin w) (x : Fin w × Path) : Fin w × Path := (e x.1, x.2)

theorem addrCompat_phi (e : Fin w ≃ Fin w) : AddrCompat (phi e) := fun _ _ => rfl

theorem under_phi_iff (e : Fin w ≃ Fin w) (x y : Fin w × Path) : Under (phi e x) (phi e y) ↔ Under x y := by
  show (e x.1 = e y.1 ∧ x.2 <+: y.2) ↔ (x.1 = y.1 ∧ x.2 <+: y.2)
  rw [e.apply_eq_iff_eq]

theorem nodeSign_conj (h : IsConjugateBy LG LH e) (x : Fin w × Path) :
    nodeSign LH.garden.sig (phi e x) = -nodeSign LG.garden.sig x := by
  show pathSign (LH.garden.sig (e x.1)) x.2 = -pathSign (LG.garden.sig x.1) x.2
  rw [h.sig_eq, pathSign_neg]

theorem layerAt_conj (h : IsConjugateBy LG LH e) (x : Fin w × Path) :
    layerAt LH (phi e x) = layerAt LG x := by
  unfold layerAt
  by_cases hx : x.2 ∈ (LG.garden.tree x.1).nodes
  · have hx' : (phi e x).2 ∈ (LH.garden.tree (phi e x).1).nodes := by
      show x.2 ∈ (LH.garden.tree (e x.1)).nodes
      rw [h.tree_eq]; exact hx
    simp only [hx, hx', dite_true]
    exact PL234.Conj.layer_node h ⟨x, hx⟩
  · have hx' : ¬ (phi e x).2 ∈ (LH.garden.tree (phi e x).1).nodes := by
      show ¬ x.2 ∈ (LH.garden.tree (e x.1)).nodes
      rw [h.tree_eq]; exact hx
    simp only [hx, hx', dite_false]

theorem parAt_conj (h : IsConjugateBy LG LH e) (p : ℕ) (x : Fin w × Path) :
    parAt LH p (phi e x) = parAt LG p x := by
  unfold parAt
  by_cases hx : x.2 ∈ (LG.garden.tree x.1).nodes
  · have hx' : (phi e x).2 ∈ (LH.garden.tree (phi e x).1).nodes := by
      show x.2 ∈ (LH.garden.tree (e x.1)).nodes
      rw [h.tree_eq]; exact hx
    simp only [hx, hx', dite_true]
    exact conj_parentLayer h p ⟨x, hx⟩
  · have hx' : ¬ (phi e x).2 ∈ (LH.garden.tree (phi e x).1).nodes := by
      show ¬ x.2 ∈ (LH.garden.tree (e x.1)).nodes
      rw [h.tree_eq]; exact hx
    simp only [hx, hx', dite_false]

theorem embeds_conj (h : IsConjugateBy LG LH e) {Q : RegCpl} {a b : Fin w × Path}
    (hE : Embeds LG.garden Q a b) :
    Embeds LH.garden (conjCpl Q) (phi e b) (phi e a) where
  indep := by
    refine ⟨fun hu => hE.indep.2 ((under_phi_iff e _ _).1 hu), fun hu => hE.indep.1 ((under_phi_iff e _ _).1 hu)⟩
  nodeA := by
    show b.2 ∈ (LH.garden.tree (e b.1)).nodes
    rw [h.tree_eq]; exact hE.nodeB
  nodeB := by
    show a.2 ∈ (LH.garden.tree (e a.1)).nodes
    rw [h.tree_eq]; exact hE.nodeA
  treeA := by
    show (LH.garden.tree (e b.1)).subtreeAt b.2 = (conjCpl Q).trees.1
    rw [h.tree_eq, trees_conjCpl]; exact hE.treeB
  treeB := by
    show (LH.garden.tree (e a.1)).subtreeAt a.2 = (conjCpl Q).trees.2
    rw [h.tree_eq, trees_conjCpl]; exact hE.treeA
  pairs := by
    intro p hp ℓ' hℓ'
    obtain ⟨q, hq, rfl⟩ := (mem_pairsAt_conjCpl (addrCompat_phi e) Q a b p).1 hp
    obtain ⟨ℓ0, rfl⟩ := (PL234.Conj.leafEquiv h).surjective ℓ'
    have h1 : q.1.2 ∈ (LG.garden.tree q.1.1).leaves :=
      hE.leaf_of_mem ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inl rfl⟩)
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

theorem cohOn_conj (h : IsConjugateBy LG LH e) (Q : RegCpl) (a b : Fin w × Path)
    (hc : CohOn LG (Q.linksAt a b)) : CohOn LH ((conjCpl Q).linksAt (phi e b) (phi e a)) := by
  have hcnt := links_countP_conjCpl (addrCompat_phi e)
    (fun x y => decide (layerAt LH x ≠ layerAt LH y)) (fun x y => by
      simp only [decide_eq_decide]; exact ne_comm) Q a b
  have h0 : (List.countP (fun l => decide (layerAt LG (l.1) ≠ layerAt LG l.2)) (Q.linksAt a b)) = 0 := by
    rw [List.countP_eq_zero]
    intro l hl
    simpa using hc l hl
  have h1 : (List.countP (fun l => decide (layerAt LH (phi e l.1) ≠ layerAt LH (phi e l.2)))
      (Q.linksAt a b)) = 0 := by
    simpa [layerAt_conj h] using h0
  rw [h1] at hcnt
  intro l hl
  have := (List.countP_eq_zero.1 hcnt) l hl
  simpa using this

end WaveTurbulence.ConjCoh
