/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ForwardBShape

/-! # Every guarded raw B expansion creates its actual source mini occurrence -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem sourceMiniB_of_raw_opB {w : ℕ} (R : Raw w) (G : Garden w) (a : Address w) (m : MiniTreeCode)
    (ha : a.2 ∈ (R.tree a.1).nodes) (he : rawOfGarden G = R.opB a m) :
    ∃ b c : GBranch G.tree, b.1 = a ∧ c.1 = addrExt a [m.c] ∧ MiniBOccurrence G b c m := by
  classical
  obtain ⟨b,c,hb,hc,hnode⟩ := branches_of_raw_opB R G a m ha he
  have hpairs : sourcePairs G = (R.opB a m).pairs := congrArg Raw.pairs he
  have hside (i j : Fin 3) (ζ : ℤˣ)
      (hm : orient (addrExt a [i]) ζ (addrExt a [m.c,j]) ∈ miniPairs R.sig a m) : LeafBond G b c i j := by
    apply leafBond_of_orient_mem G b c i j ζ
    have hx : (b.child i).1 = addrExt a [i] := congrArg (fun z : Address w => addrExt z [i]) hb
    have hy : (c.child j).1 = addrExt a [m.c,j] := by
      change addrExt c.1 [j] = _
      rw [hc,addrExt_append]
      rfl
    rw [hx,hy,hpairs]
    change _ ∈ _ ∪ miniPairs R.sig a m
    exact Finset.mem_union_right _ hm
  refine ⟨b,c,hb,hc,hnode,?_,?_⟩
  · exact hside m.red.1 m.red.2 _ (Finset.mem_insert_self _ _)
  · exact hside m.green.1 m.green.2 _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

end WaveTurbulence.Reg.Skeleton
