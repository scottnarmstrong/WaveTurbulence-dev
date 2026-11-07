/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueData3
import Mathlib.Tactic

/-!
# The glue hypotheses for reconstruction data
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

/-- **`GlueC` for the couple slot `q` of reconstruction data `F`.** -/
theorem glueC_ofData {S : Garden w} (F : ReconstructionData S) (hS : S.IsPlain) (q : SourcePair S)
    (LN T : LayeredGarden w) (hLN : LN.garden = (F.eraseCouple q).garden hS)
    (aT bT : Fin w × Path) (p : ℕ)
    (embT : Embeds T.garden (F.couple q) aT bT)
    (hpa : parAt T p aT = parAt LN p (inflatedPosition S F.tree (q.firstLeaf hS).toNode))
    (hpb : parAt T p bT = parAt LN p (inflatedPosition S F.tree (q.secondLeaf hS).toNode))
    (hp : ∀ n, T.layer n ≤ p) :
    GlueC LN T (F.garden hS) (F.couple q) (inflatedPosition S F.tree (q.firstLeaf hS).toNode)
      (inflatedPosition S F.tree (q.secondLeaf hS).toNode) aT bT p := by
  obtain ⟨G0, l0, hl0⟩ := LN
  change G0 = _ at hLN
  subst hLN
  have embN := reconstruction_coupleEmb (F.eraseCouple q) hS ((F.eraseCouple q).garden_decodes hS) q
  rw [F.eraseCouple_at q] at embN
  have embM := reconstruction_coupleEmb F hS (F.garden_decodes hS) q
  have hf := data_couple_outside F hS q
  exact ⟨embM.indep, embN, embM, embT, hf.1, hf.2.1, hf.2.2, hpa, hpb, hp⟩

/-- **`GlueT` for the tree slot `b` of reconstruction data `F`.** -/
theorem glueT_ofData {S : Garden w} (F : ReconstructionData S) (hS : S.IsPlain) (b : GBranch S.tree)
    (LM T : LayeredGarden w) (hLM : LM.garden = (F.eraseTree b).garden hS)
    (aT : Fin w × Path) (t' : TTree) (p : ℕ)
    (embT : ChainEmb T.garden (F.tree b) (nodeSign S.sig b.1) aT t')
    (hpa : parAt T p aT = parAt LM p (inflatedPosition S F.tree b.toNode))
    (hlone : layerAt T (addrExt aT (F.tree b).lonePath) =
      layerAt LM (inflatedPosition S F.tree b.toNode))
    (hp : ∀ n, T.layer n ≤ p) :
    GlueT LM T ((F.garden hS)) (F.tree b) (nodeSign S.sig b.1) (inflatedPosition S F.tree b.toNode) aT
      (node3 (fun i => F.inflateNode hS (b.child i))) t' p := by
  obtain ⟨G0, l0, hl0⟩ := LM
  change G0 = _ at hLM
  subst hLM
  have embM := reconstruction_chainEmb (F.eraseTree b) hS ((F.eraseTree b).garden_decodes hS) b
  rw [F.eraseTree_at b, F.eraseTree_position_at b] at embM
  have e : (fun i => (F.eraseTree b).inflateNode hS (b.child i)) = fun i => F.inflateNode hS (b.child i) :=
    funext (F.eraseTree_inflateNode_child hS b)
  rw [e] at embM
  have embG := reconstruction_chainEmb F hS (F.garden_decodes hS) b
  have hf := data_tree_outside F hS b
  exact ⟨embM, embG, embT, hf.1, hf.2.1, hf.2.2, hpa, hlone, hp⟩

end WaveTurbulence.Stage1
