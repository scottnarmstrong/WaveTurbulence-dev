/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueC11
import Mathlib.Tactic

/-!
# Gluing a template regular tree into a layered base (address level)

The tree analogue of `GlueC`.  The base `LM` carries the nil tree at `a` (so the subtree `t` hangs at `a`);
the glued garden `G2` carries `X` at `a` with `t` moved to `n' = a·lone(X)`.  Inside the tree region
(`InTree a n'`) the layers are the template's; elsewhere they are the base's after moving the subtree at `n'`
back to `a`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

open scoped Classical in
/-- Layer of the glued garden (tree case). -/
@[expose] noncomputable def glueTAt (LM T : LayeredGarden w) (a aT n : Fin w × Path) (z : Fin w × Path) : ℕ :=
  if InTree a n z then layerAt T (addrExt aT (z.2.drop a.2.length)) else layerAt LM (shiftAddr n a z)

theorem glueTAt_in (LM T : LayeredGarden w) (a aT n : Fin w × Path) {z : Fin w × Path}
    (h : InTree a n z) : glueTAt LM T a aT n z = layerAt T (addrExt aT (z.2.drop a.2.length)) := by
  unfold glueTAt; simp only [h, ↓reduceIte]

theorem glueTAt_out (LM T : LayeredGarden w) (a aT n : Fin w × Path) {z : Fin w × Path}
    (h : ¬ InTree a n z) : glueTAt LM T a aT n z = layerAt LM (shiftAddr n a z) := by
  unfold glueTAt; simp only [h, ↓reduceIte]

theorem glueTAt_ext (LM T : LayeredGarden w) (a aT n : Fin w × Path) (hn : Under a n) (q : Path)
    (h : ¬ Under n (addrExt a q)) :
    glueTAt LM T a aT n (addrExt a q) = layerAt T (addrExt aT q) := by
  rw [glueTAt_in _ _ _ _ _ ⟨under_ext a q, h⟩]
  simp [addrExt]

/-- Hypotheses for gluing the template regular tree `X` (at `aT`, subtree `t'` at its lone position) into the
base `LM` (nil tree at `a`, subtree `t`), producing a layering of the garden `G2` (`X` at `a`). -/
structure GlueT (LM T : LayeredGarden w) (G2 : Garden w) (X : RegChain) (ζ : ℤˣ) (a aT : Fin w × Path)
    (t t' : TTree) (p : ℕ) : Prop where
  embM : ChainEmb LM.garden .nil ζ a t
  embG : ChainEmb G2 X ζ a t
  embT : ChainEmb T.garden X ζ aT t'
  node : ∀ z, z.2 ∈ (LM.garden.tree z.1).nodes ↔
    (shiftAddr a (addrExt a X.lonePath) z).2 ∈ (G2.tree (shiftAddr a (addrExt a X.lonePath) z).1).nodes
  leaf : ∀ z, z.2 ∈ (LM.garden.tree z.1).leaves ↔
    (shiftAddr a (addrExt a X.lonePath) z).2 ∈ (G2.tree (shiftAddr a (addrExt a X.lonePath) z).1).leaves
  pair : ∀ (ℓ : GLeaf LM.garden.tree) (ℓ' : GLeaf G2.tree),
    shiftAddr a (addrExt a X.lonePath) ℓ.1 = ℓ'.1 →
    shiftAddr a (addrExt a X.lonePath) (LM.garden.pair ℓ).1 = (G2.pair ℓ').1
  hpa : parAt T p aT = parAt LM p a
  hlone : layerAt T (addrExt aT X.lonePath) = layerAt LM a
  hp : ∀ n, T.layer n ≤ p

end WaveTurbulence.Stage1
