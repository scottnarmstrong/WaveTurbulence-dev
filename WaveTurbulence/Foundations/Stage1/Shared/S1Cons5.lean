/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Cons4
import Mathlib.Tactic

/-!
# Glue specification: the assembled `LFConstruction`
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w}

theorem oat_congr {LM LH : LayeredGarden w} {a a' n n' m m' : Address w} (ea : a = a') (en : n = n')
    (em : m = m') (h : OutAgreeT LM LH a n m) : OutAgreeT LM LH a' n' m' := by
  subst ea; subst en; subst em; exact h

theorem ce_congr {G : Garden w} {ζ : ℤˣ} {t : TTree} {a a' : Address w} {X X' : RegChain}
    (ea : a = a') (eX : X = X') (h : ChainEmb G X ζ a t) : ChainEmb G X' ζ a' t := by
  subst ea; subst eX; exact h

namespace GlueSpec
variable {s : LFSource p kind LG} {ε : Bool} (g : GlueSpec s ε)

theorem pins (hk : K2Pins s ε)
    (hplug : ∀ b : GBranch s.skeleton.tree, b ≠ s.placement.lower →
      ∀ q ∈ ((s.data.tree b).plug (nodeSign s.skeleton.sig b.1) .leaf).nodes,
        q ∈ (((s.baseData ε).tree (s.branches ε b)).plug (nodeSign (s.chosen ε).sig (s.branches ε b).1) .leaf).nodes) :
    (∀ b : GBranch s.skeleton.tree, layerAt LG (s.data.corePosition b) =
      layerAt g.glued2 (g.FD.corePosition (s.branches ε b))) ∧
    (∀ b : GBranch s.skeleton.tree, b ≠ s.placement.lower →
      ∀ q ∈ ((s.data.tree b).plug (nodeSign s.skeleton.sig b.1) .leaf).nodes,
      layerAt LG (addrExt (inflatedPosition s.skeleton s.data.tree b.toNode) q) =
        layerAt g.glued2 (addrExt (inflatedPosition (s.chosen ε) g.FD.tree (s.branches ε b).toNode) q)) ∧
    (∀ q : SourcePair s.skeleton, q ≠ s.exceptional → ∀ (i : Fin 2) (r : Path),
      r ∈ ((decodedCouple (s.data.couple q)).tree i).nodes →
      layerAt LG (addrExt (coupleRoot s.data s.plain q i) r) =
        layerAt g.glued2 (addrExt (coupleRoot g.FD (s.chosen_plain ε) (s.pairs ε q) i) r)) := by
  refine pins_of_records s ε hk hplug g.X g.Q g.hX g.hQ g.glued1 g.glued2 (ζ := nodeSign (s.chosen ε).sig
    (s.branches ε s.placement.lower).1) (t := node3 (fun i => g.FD.inflateNode (s.chosen_plain ε)
      ((s.branches ε s.placement.lower).child i))) ((s.midData ε g.Q g.hQ).garden_decodes _)
    (g.FD.garden_decodes _) g.glueC.outAgree ?_ ?_
  · have := g.glueT.embM
    exact ce_congr (X := RegChain.nil) g.pos_FD rfl this
  · have := g.glueT.outAgreeT
    refine oat_congr g.pos_FD ?_ ?_ this
    · simp [RegChain.lonePath, addrExt, g.pos_FD]; rfl
    · rw [g.FD_tree_lower, g.pos_FD]; rfl

/-- **The glued `LFConstruction`.** -/
@[expose] noncomputable def construction (hk : K2Pins s ε)
    (hplug : ∀ b : GBranch s.skeleton.tree, b ≠ s.placement.lower →
      ∀ q ∈ ((s.data.tree b).plug (nodeSign s.skeleton.sig b.1) .leaf).nodes,
        q ∈ (((s.baseData ε).tree (s.branches ε b)).plug (nodeSign (s.chosen ε).sig (s.branches ε b).1) .leaf).nodes)
    (hord : g.X.size + g.Q.size = (s.data.tree s.placement.lower).size + (s.data.couple s.exceptional).size)
    (hcnt : rawTreeLayerCount LG s.data s.plain p s.placement.lower +
        rawCoupleLayerCount LG s.data s.plain p s.exceptional =
      rawTreeLayerCount g.glued2 g.FD (s.chosen_plain ε) p (s.branches ε s.placement.lower) +
      rawCoupleLayerCount g.glued2 g.FD (s.chosen_plain ε) p (s.pairs ε s.exceptional)) :
    LFConstruction s ε where
  newTree := g.X
  newCouple := g.Q
  tree_wf := g.hX
  couple_wf := g.hQ
  midLayer := g.glued1.layer
  mid_isLayering := g.glued1.isLayering
  outLayer := g.glued2.layer
  out_isLayering := g.glued2.isLayering
  tail := node3 (fun i => g.FD.inflateNode (s.chosen_plain ε) ((s.branches ε s.placement.lower).child i))
  coupleInsertion := g.coupleInsertion_aux
  treeInsertion := g.treeInsertion_aux
  coreLayers := (g.pins hk hplug).1
  ordinaryTreeLayers := (g.pins hk hplug).2.1
  ordinaryCoupleLayers := (g.pins hk hplug).2.2
  combinedOrder := hord
  combinedTopCount := hcnt

end GlueSpec
end WaveTurbulence.Stage1
