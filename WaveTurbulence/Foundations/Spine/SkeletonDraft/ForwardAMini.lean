/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ForwardAShape

/-! # Every guarded raw A expansion creates its actual source mini occurrence -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem miniA_oriented_mem {w : ℕ} (x y : Address w) (k : MiniCplCode) (i : Fin 3) :
    orient (addrExt x [i]) (slotSign (1 : ℤˣ) i) (addrExt y [k.partner i]) ∈
      ({(addrExt x [0],addrExt y [k.partner 0]),
       (addrExt y [1],addrExt x [1]),(addrExt x [2],addrExt y [k.partner 2])} : Finset (Pair w)) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> fin_cases k <;> simp [orient,slotSign,MiniCplCode.partner]

theorem sourceMiniA_of_raw_opA {w : ℕ} (R : Raw w) (hR : R.Valid) (G : Garden w)
    (x y : Address w) (k : MiniCplCode) (hp : (x,y) ∈ R.pairs)
    (he : rawOfGarden G = R.opA x y k) :
    ∃ b c : GBranch G.tree, b.1 = x ∧ c.1 = y ∧ MiniAOccurrence G b c k := by
  classical
  obtain ⟨b,c,hb,hc⟩ := branches_of_raw_opA R hR G x y k hp he
  have hv := hR.1 _ hp
  have hsig : G.sig = R.sig := congrArg Raw.sig he
  have hpos : G.sign b.toNode = 1 := by
    change nodeSign G.sig b.1 = 1
    rw [hb,hsig]
    exact hv.2.2.1
  have hneg : G.sign c.toNode = -1 := by
    change nodeSign G.sig c.1 = -1
    rw [hc,hsig]
    exact hv.2.2.2
  have hpairs : sourcePairs G = (R.opA x y k).pairs := congrArg Raw.pairs he
  refine ⟨b,c,hb,hc,?_,?_⟩
  · rw [hpos,hneg]
  · intro i
    apply leafBond_of_orient_mem G b c i (k.partner i) (slotSign 1 i)
    have hx : (b.child i).1 = addrExt x [i] := congrArg (fun z : Address w => addrExt z [i]) hb
    have hy : (c.child (k.partner i)).1 = addrExt y [k.partner i] :=
      congrArg (fun z : Address w => addrExt z [k.partner i]) hc
    rw [hx,hy,hpairs]
    change _ ∈ _ ∪ _
    exact Finset.mem_union_right _ (miniA_oriented_mem x y k i)

end WaveTurbulence.Reg.Skeleton
