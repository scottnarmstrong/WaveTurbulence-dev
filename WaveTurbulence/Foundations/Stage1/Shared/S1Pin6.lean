/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Pin5
import Mathlib.Tactic

/-!
# The three pin fields of an LF construction from the two insertion records
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w}

/-- The pin fields of an `LFConstruction`, for arbitrary `out` decoded by the final data. -/
theorem pins_of_records (s : LFSource p kind LG) (ε : Bool) (hk : K2Pins s ε)
    (hplug : ∀ b : GBranch s.skeleton.tree, b ≠ s.placement.lower →
      ∀ q ∈ ((s.data.tree b).plug (nodeSign s.skeleton.sig b.1) .leaf).nodes,
        q ∈ (((s.baseData ε).tree (s.branches ε b)).plug (nodeSign (s.chosen ε).sig (s.branches ε b).1) .leaf).nodes)
    (X : RegChain) (Q : RegCpl) (hX : X.wf = true) (hQ : Q.wf = true)
    (mid out : LayeredGarden w) {ζ : ℤˣ} {t : TTree}
    (hmid : (s.midData ε Q hQ).Decodes (s.chosen_plain ε) mid.garden)
    (hout : (s.finalData ε X Q hX hQ).Decodes (s.chosen_plain ε) out.garden)
    (hc : OutAgree (s.base ε) mid
      (inflatedPosition (s.chosen ε) (s.baseData ε).tree ((s.pairs ε s.exceptional).firstLeaf (s.chosen_plain ε)).toNode)
      (inflatedPosition (s.chosen ε) (s.baseData ε).tree ((s.pairs ε s.exceptional).secondLeaf (s.chosen_plain ε)).toNode))
    (hemb : ChainEmb mid.garden .nil ζ (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode) t)
    (hT : OutAgreeT mid out (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode)
      (addrExt (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode) RegChain.nil.lonePath)
      (addrExt (inflatedPosition (s.chosen ε) (s.baseData ε).tree (s.branches ε s.placement.lower).toNode) X.lonePath)) :
    (∀ b : GBranch s.skeleton.tree, layerAt LG (s.data.corePosition b) =
      layerAt out ((s.finalData ε X Q hX hQ).corePosition (s.branches ε b))) ∧
    (∀ b : GBranch s.skeleton.tree, b ≠ s.placement.lower →
      ∀ q ∈ ((s.data.tree b).plug (nodeSign s.skeleton.sig b.1) .leaf).nodes,
      layerAt LG (addrExt (inflatedPosition s.skeleton s.data.tree b.toNode) q) =
        layerAt out (addrExt (inflatedPosition (s.chosen ε) (s.finalData ε X Q hX hQ).tree
          (s.branches ε b).toNode) q)) ∧
    (∀ q : SourcePair s.skeleton, q ≠ s.exceptional → ∀ (i : Fin 2) (r : Path),
      r ∈ ((decodedCouple (s.data.couple q)).tree i).nodes →
      layerAt LG (addrExt (coupleRoot s.data s.plain q i) r) =
        layerAt out (addrExt (coupleRoot (s.finalData ε X Q hX hQ) (s.chosen_plain ε) (s.pairs ε q) i) r)) := by
  have hk3 := k3_pins (s.baseData ε) (s.chosen_plain ε) (s.branches ε s.placement.lower)
    (s.pairs ε s.exceptional) Q X hQ hX (baseData_tree_lower s ε) (s.base ε) mid out hmid hout hc hemb hT
  refine ⟨fun b => (hk.1 b).trans (hk3.1 _).symm, fun b hb q hq => (hk.2.1 b hb q hq).trans ?_,
    fun q hq i r hr => (hk.2.2 q hq i r hr).trans ?_⟩
  · have hne : s.branches ε b ≠ s.branches ε s.placement.lower := fun he => hb ((s.branches ε).injective he)
    exact (hk3.2.1 _ hne q (hplug b hb q hq)).symm
  · have hne : s.pairs ε q ≠ s.pairs ε s.exceptional := fun he => hq ((s.pairs ε).injective he)
    exact (hk3.2.2 _ hne i r).symm

end WaveTurbulence.Stage1
