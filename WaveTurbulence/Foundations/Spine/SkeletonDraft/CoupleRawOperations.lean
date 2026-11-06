/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CoupleRawCarrier

/-! # Pinned regular-couple A/B histories commute with the exact finite-pair carrier -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem nodup_toFinset_erase {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α] (l : List α) (hn : l.Nodup) (a : α) :
    (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp only [List.mem_toFinset,hn.mem_erase_iff,Finset.mem_erase]

theorem rawCplSet_opA (R : RawCpl) (hn : R.2.Nodup) (x y : Address 2) (k : MiniCplCode) :
    rawCplSet (R.opA x y k) = (rawCplSet R).opA x y k := by
  classical
  apply Raw.ext
  · rfl
  · have ht := raw_opA_updates R x y k
    simpa only [rawCplSet,Raw.opA,updateAddressForest,setAt_eq_replaceAt] using ht
  · change ((R.2.erase (x,y)) ++
      [(addrExt x [0],addrExt y [k.partner 0]),(addrExt y [1],addrExt x [1]),
       (addrExt x [2],addrExt y [k.partner 2])]).toFinset = _
    rw [List.toFinset_append]
    simp only [Raw.opA,rawCplSet]
    rw [nodup_toFinset_erase R.2 hn (x,y)]
    simp


theorem rawCplSet_opB (R : RawCpl) (a : Address 2) (m : MiniTreeCode) :
    rawCplSet (R.opB a m) = (rawCplSet R).opB a m := by
  classical
  apply Raw.ext
  · rfl
  · have ht := raw_opB_update R a m
    simpa only [rawCplSet,Raw.opB,updateAddressForest,setAt_eq_replaceAt,miniTreeContext] using ht
  · ext p
    simp [rawCplSet,Raw.opB,RawCpl.opB,RawCpl.relocate,RawCpl.orient,
      relocate,orient,miniPairs,List.mem_toFinset,Finset.mem_image]
    rfl

theorem RawRegular.pairs_nodup {R : RawCpl} (hR : RawRegular R) : R.2.Nodup := by
  obtain ⟨Q,_,hrep⟩ := RawRegular.exists_wf_rawRep hR
  exact hrep.2.nodup_iff.mpr (decodedPair_nodup Q)

end WaveTurbulence.Reg.Skeleton
