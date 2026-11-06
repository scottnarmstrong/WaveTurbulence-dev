/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.ExplicitCoherentApps
/-! Literal conjugate-object and top-branch-count data for TARGET Prop 6.3, L1118–1125. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open TTree

/-- Transport a node along an exact root permutation, preserving its path. -/
def reindexedNode {w : ℕ} (G H : Garden w) (e : Fin w ≃ Fin w)
    (htree : ∀ i, H.tree (e i) = G.tree i) (a : GNode G.tree) : GNode H.tree :=
  ⟨(e a.1.1, a.1.2), by rw [htree]; exact a.2⟩

def reindexedLeaf {w : ℕ} (G H : Garden w) (e : Fin w ≃ Fin w)
    (htree : ∀ i, H.tree (e i) = G.tree i) (ℓ : GLeaf G.tree) : GLeaf H.tree :=
  ⟨(e ℓ.1.1, ℓ.1.2), by rw [htree]; exact ℓ.2⟩

/-- TARGET deftree L631 and defgarden L636: opposite root signs, identical tree paths,
pairings and marks transported by e, and the same node layers. -/
structure IsConjugateBy {w : ℕ} (LG LH : LayeredGarden w) (e : Fin w ≃ Fin w) : Prop where
  tree_eq : ∀ i, LH.garden.tree (e i) = LG.garden.tree i
  sig_eq : ∀ i, LH.garden.sig (e i) = -LG.garden.sig i
  mark_eq : ∀ ℓ : GLeaf LG.garden.tree,
    LH.garden.mark (reindexedLeaf LG.garden LH.garden e tree_eq ℓ) = LG.garden.mark ℓ
  pair_eq : ∀ ℓ : GLeaf LG.garden.tree,
    (LH.garden.pair (reindexedLeaf LG.garden LH.garden e tree_eq ℓ)).1 =
      (e (LG.garden.pair ℓ).1.1, (LG.garden.pair ℓ).1.2)
  layer_eq : ∀ a : GNode LG.garden.tree,
    LH.layer (reindexedNode LG.garden LH.garden e tree_eq a) = LG.layer a

/-- Conjugating a (+,-) couple exchanges its two trees as well as reversing signs. -/
abbrev IsConjugateCouple (LG LH : LayeredGarden 2) : Prop :=
  IsConjugateBy LG LH (Equiv.swap (0 : Fin 2) 1)

/-- Conjugating a paired tree preserves its root position and reverses the sign. -/
abbrev IsConjugateTree (LG LH : LayeredGarden 1) : Prop := IsConjugateBy LG LH (Equiv.refl (Fin 1))

/-- Number of branching nodes in the fixed top layer p (layerregest10, final sentence). -/
def topBranchCount {w : ℕ} (LG : LayeredGarden w) (p : ℕ) : ℕ :=
  ((Finset.univ : Finset (GBranch LG.garden.tree)).filter fun b => LG.layer b.toNode = p).card

/-- The exact summation carrier of layerregest10. b=none is the unrestricted sum;
b=some m imposes the optional fixed total number of layer-p branching nodes. -/
def CoherentPairCarrier (p q q' n : ℕ) (b : Option ℕ)
    (Q : RegCpl) (X : RegChain) (LQ : LayeredGarden 2) (LX : LayeredGarden 1) : Prop :=
  IsCoherentCoupleAt p q q' Q LQ ∧ IsCoherentTreeAt p q q' X LX ∧
    LX.garden.sig 0 = 1 ∧ LQ.garden.order + LX.garden.order = 2 * n ∧
    match b with
    | none => True
    | some m => topBranchCount LQ p + topBranchCount LX p = m

end WaveTurbulence.LGSpine
