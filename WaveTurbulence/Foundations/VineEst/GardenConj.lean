/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.CoherentConjugacyData

/-!
# The conjugate garden along a root permutation (CONJ-COH)

TARGET deftree/defgarden: the conjugate of a layered garden `LG` along `e : Fin w ≃ Fin w` has the tree of `LG`
at root `e i` in place of root `i`, the opposite root signs, the pairing and marks transported, and the same
layers.  `conjLayered LG e` is such a garden and `conjLayered_isConjugateBy` shows it satisfies the
`IsConjugateBy` relation of `CoherentConjugacyData`.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.ConjCoh

open WaveTurbulence TTree WaveTurbulence.LGSpine

variable {w : ℕ}

theorem pathSign_neg (ζ : ℤˣ) (p : Path) : pathSign (-ζ) p = -pathSign ζ p := by
  simp [pathSign]

/-- The leaf of the original forest corresponding to a leaf of the relabelled forest. -/
def leafBack (G : Garden w) (e : Fin w ≃ Fin w) (ℓ : GLeaf (fun j => G.tree (e.symm j))) :
    GLeaf G.tree := ⟨(e.symm ℓ.1.1, ℓ.1.2), ℓ.2⟩

/-- The leaf of the relabelled forest corresponding to a leaf of the original forest. -/
def leafFwd (G : Garden w) (e : Fin w ≃ Fin w) (ℓ : GLeaf G.tree) :
    GLeaf (fun j => G.tree (e.symm j)) :=
  ⟨(e ℓ.1.1, ℓ.1.2), by
    show ℓ.1.2 ∈ (G.tree (e.symm (e ℓ.1.1))).leaves
    rw [e.symm_apply_apply]; exact ℓ.2⟩

theorem leafBack_fwd (G : Garden w) (e : Fin w ≃ Fin w) (ℓ : GLeaf G.tree) :
    leafBack G e (leafFwd G e ℓ) = ℓ := Subtype.ext (Prod.ext (e.symm_apply_apply _) rfl)

theorem leafFwd_back (G : Garden w) (e : Fin w ≃ Fin w) (ℓ : GLeaf (fun j => G.tree (e.symm j))) :
    leafFwd G e (leafBack G e ℓ) = ℓ := Subtype.ext (Prod.ext (e.apply_symm_apply _) rfl)

/-- The conjugate garden along `e`. -/
def conjGarden (G : Garden w) (e : Fin w ≃ Fin w) : Garden w where
  sig j := -G.sig (e.symm j)
  tree j := G.tree (e.symm j)
  pair ℓ := leafFwd G e (G.pair (leafBack G e ℓ))
  mark ℓ := G.mark (leafBack G e ℓ)
  pair_pair ℓ := by
    simp only [leafBack_fwd, G.pair_pair, leafFwd_back]
  pair_eq_iff ℓ := by
    have h := G.pair_eq_iff (leafBack G e ℓ)
    constructor
    · intro hp
      apply h.1
      have := congrArg (leafBack G e) hp
      simpa [leafBack_fwd] using this
    · intro hm
      have := h.2 hm
      calc leafFwd G e (G.pair (leafBack G e ℓ)) = leafFwd G e (leafBack G e ℓ) := by rw [this]
        _ = ℓ := leafFwd_back G e ℓ
  pair_sign ℓ hne := by
    have hne' : G.pair (leafBack G e ℓ) ≠ leafBack G e ℓ := by
      intro hp
      apply hne
      calc leafFwd G e (G.pair (leafBack G e ℓ)) = leafFwd G e (leafBack G e ℓ) := by rw [hp]
        _ = ℓ := leafFwd_back G e ℓ
    have := G.pair_sign _ hne'
    simp only [nodeSign, leafFwd, leafBack, Equiv.symm_apply_apply, pathSign_neg] at this ⊢
    rw [this]


theorem conjGarden_tree (G : Garden w) (e : Fin w ≃ Fin w) (i : Fin w) :
    (conjGarden G e).tree (e i) = G.tree i := by
  show G.tree (e.symm (e i)) = G.tree i
  rw [e.symm_apply_apply]

/-- The layers of the conjugate garden. -/
def layerConj (LG : LayeredGarden w) (e : Fin w ≃ Fin w) (a : GNode (conjGarden LG.garden e).tree) : ℕ :=
  LG.layer ⟨(e.symm a.1.1, a.1.2), a.2⟩

theorem layerConj_leafFwd (LG : LayeredGarden w) (e : Fin w ≃ Fin w) (x : GLeaf LG.garden.tree) :
    layerConj LG e (leafFwd LG.garden e x).toNode = LG.layer x.toNode := by
  show LG.layer ⟨(e.symm (e x.1.1), x.1.2), _⟩ = _
  congr 1
  exact Subtype.ext (Prod.ext (e.symm_apply_apply _) rfl)

/-- The conjugate layered garden along `e`: same layers, transported. -/
def conjLayered (LG : LayeredGarden w) (e : Fin w ≃ Fin w) : LayeredGarden w where
  garden := conjGarden LG.garden e
  layer := layerConj LG e
  isLayering := by
    refine ⟨fun b i => LG.isLayering.1 ⟨(e.symm b.1.1, b.1.2), b.2⟩ i, fun ℓ => ?_⟩
    have h := LG.isLayering.2 (leafBack LG.garden e ℓ)
    show layerConj LG e ℓ.toNode = layerConj LG e
      (leafFwd LG.garden e (LG.garden.pair (leafBack LG.garden e ℓ))).toNode
    rw [layerConj_leafFwd]; exact h

theorem leafBack_reindexed (LG : LayeredGarden w) (e : Fin w ≃ Fin w)
    (htree : ∀ i, (conjLayered LG e).garden.tree (e i) = LG.garden.tree i) (ℓ : GLeaf LG.garden.tree) :
    leafBack LG.garden e (reindexedLeaf LG.garden (conjLayered LG e).garden e htree ℓ) = ℓ :=
  Subtype.ext (Prod.ext (e.symm_apply_apply _) rfl)

theorem conjLayered_isConjugateBy (LG : LayeredGarden w) (e : Fin w ≃ Fin w) :
    IsConjugateBy LG (conjLayered LG e) e where
  tree_eq := conjGarden_tree LG.garden e
  sig_eq i := by
    show -LG.garden.sig (e.symm (e i)) = -LG.garden.sig i
    rw [e.symm_apply_apply]
  mark_eq ℓ := by
    exact congrArg LG.garden.mark (leafBack_reindexed LG e _ ℓ)
  pair_eq ℓ := by
    exact (congrArg (fun x => (leafFwd LG.garden e (LG.garden.pair x)).1)
      (leafBack_reindexed LG e _ ℓ)).trans rfl
  layer_eq a := by
    show LG.layer ⟨(e.symm (e a.1.1), a.1.2), _⟩ = LG.layer a
    congr 1
    exact Subtype.ext (Prod.ext (e.symm_apply_apply _) rfl)

end WaveTurbulence.ConjCoh
