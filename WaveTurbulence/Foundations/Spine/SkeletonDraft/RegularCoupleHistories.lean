/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CoupleRawOperations

/-! # Exact finite A/B reconstruction histories for the pinned source regular couples -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem RawRegular.reconstructs {R : RawCpl} (hR : RawRegular R) :
    Reconstructs (rawCplSet ((.leaf,.leaf),[((0,[]),(1,[]))])) (rawCplSet R) := by
  induction hR with
  | triv => exact Relation.ReflTransGen.refl
  | @opA R x y k hr hp ih =>
    rw [rawCplSet_opA R (RawRegular.pairs_nodup hr) x y k]
    exact ih.tail (Expand.opA _ x y k (rawCplSet_valid_of_regular hr) (List.mem_toFinset.mpr hp))
  | @opB R a m hr ha ih =>
    rw [rawCplSet_opB R a m]
    exact ih.tail (Expand.opB _ a m (rawCplSet_valid_of_regular hr) ha)

theorem rawOfGarden_eq_regular_history (G : Garden 2) (R : RawCpl)
    (hR : RawRegular R) (hm : G.MatchesCouple R.1 R.2) : rawOfGarden G = rawCplSet R := by
  obtain ⟨Q,_,hrep⟩ := RawRegular.exists_wf_rawRep hR
  have hd : Q.Decodes G := (hrep.decodes_iff G).mpr hm
  exact (rawOfGarden_eq_code_raw hd).trans (RawRep.rawCplSet_eq hrep).symm

/-- A source regular couple has an actual guarded finite A/B history from the trivial source couple. -/
theorem regularCouple_reconstructs {G : Garden 2} (hG : IsRegularCouple G) :
    Reconstructs (rawCplSet ((.leaf,.leaf),[((0,[]),(1,[]))])) (rawOfGarden G) := by
  obtain ⟨R,hR,hm⟩ := hG
  rw [rawOfGarden_eq_regular_history G R hR hm]
  exact RawRegular.reconstructs hR

end WaveTurbulence.Reg.Skeleton
