/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Fold2
public import WaveTurbulence.Foundations.FinalCount.RedSpliceIter
import Mathlib.Tactic

/-!
# VINE-B Part I (3): the fold invariant

`FoldInv P st` records, for the splice state `st` of `G0` obtained by splicing the blocks `u` with `P u`, the node
map `node : GNode st.G.tree → GNode G0.tree` with the properties of `SpliceShape` (the blocks being those with `P`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.Mole WaveTurbulence.RegRed WaveTurbulence.RedSplice

variable {w : ℕ} {G0 : Garden w}

/-- Retained nodes of `G0` with respect to the blocks satisfying `P`. -/
def RetP (P : CLBlock G0 → Prop) (x : GNode G0.tree) : Prop :=
  ∀ u : CLBlock G0, P u → x ∉ clRealizationNodes G0 u.atoms ∨ x = u.upper.toNode

structure FoldInv (P : CLBlock G0 → Prop) (st : SpState G0) where
  node : GNode st.G.tree → GNode G0.tree
  inj : Function.Injective node
  range : ∀ x, (∃ y, node y = x) ↔ RetP P x
  tree_eq : ∀ y, (node y).1.1 = y.1.1
  root : ∀ y, (node y).1.2 = [] ↔ y.1.2 = []
  br_node : ∀ c : GBranch st.G.tree, (st.M.ob c).toNode = node c.toNode
  leaf : GLeaf st.G.tree → GLeaf G0.tree
  leaf_node : ∀ ℓ, (leaf ℓ).toNode = node ℓ.toNode
  pair : ∀ ℓ, leaf (st.G.pair ℓ) = G0.pair (leaf ℓ)
  mark : ∀ ℓ, st.G.mark ℓ = G0.mark (leaf ℓ)
  parentL : ∀ (ℓ : GLeaf st.G.tree) (hn : ℓ.1.2 ≠ []) (ho : (leaf ℓ).1.2 ≠ []),
    st.M.ob (GNode.parent ℓ.toNode hn) = repC st.cls (GNode.parent (leaf ℓ).toNode ho)
  sign : ∀ y, G0.sign (node y) = st.G.sign y
  child : ∀ (c : GBranch st.G.tree) (i : Fin 3), (∀ u : CLBlock G0, P u → st.M.ob c ≠ u.upper) →
    node (c.child i) = (st.M.ob c).child i
  crown : ∀ (c : GBranch st.G.tree) (u : CLBlock G0), P u → st.M.ob c = u.upper → ∀ i : Fin 3,
    node (c.child i) ∈ crownSet u
  cls_none : ∀ v, st.cls v = none ↔ ∀ u : CLBlock G0, P u → v ∉ u.atoms

/-- The empty splice. -/
noncomputable def FoldInv.init (G0 : Garden w) : FoldInv (fun _ => False) (SpState.init G0) where
  node := id
  inj := Function.injective_id
  range := fun x => ⟨fun _ u hu => hu.elim, fun _ => ⟨x, rfl⟩⟩
  tree_eq := fun _ => rfl
  root := fun _ => Iff.rfl
  br_node := fun _ => rfl
  leaf := id
  leaf_node := fun _ => rfl
  pair := fun _ => rfl
  mark := fun _ => rfl
  parentL := fun _ _ _ => rfl
  sign := fun _ => rfl
  child := fun _ _ _ => rfl
  crown := fun _ _ h => h.elim
  cls_none := fun v => ⟨fun _ u hu => hu.elim, fun _ => rfl⟩

/-- The invariant depends on `P` only up to equivalence. -/
noncomputable def FoldInv.congr {P P' : CLBlock G0 → Prop} {st : SpState G0} (h : ∀ u, P u ↔ P' u)
    (T : FoldInv P st) : FoldInv P' st := by
  have : P = P' := funext fun u => propext (h u)
  subst this
  exact T

end WaveTurbulence.VineB
