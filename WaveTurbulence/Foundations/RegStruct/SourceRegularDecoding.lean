/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.OperationBFidelity

/-! # Every source-regular couple has well-formed structure data

This direction is induction on the actual A/B construction history. Both
operation cases consume literal source positions and retain full raw trees
and pair-list multiplicities.
-/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Source operation B preserves exact representation at every actual node. -/
theorem rawRep_opB {Q : RegCpl} {R : RawCpl} (h : RawRep Q R)
    (a : Fin 2 × Path) (m : MiniTreeCode) (ha : a.2 ∈ (R.tree a.1).nodes) :
    RawRep (operationB Q a m) (R.opB a m) := by
  have ht : a ∈ coupleNodes Q (0,[]) (1,[]) := by
    apply (coupleForest_node_iff Q a).mp
    simpa only [h.forest] using ha
  have hfR := raw_opB_update R a m
  have hfQ := raw_opB_update Q.raw a m
  simp only [h.forest] at hfR
  simp only [raw_tree_eq_coupleForest] at hfQ
  have hf : (R.opB a m).tree = coupleForest (operationB Q a m) :=
    hfR.trans (hfQ.symm.trans (operationB_forest Q a m ht).symm)
  constructor
  · have h0 := congrFun hf (0 : Fin 2)
    have h1 := congrFun hf (1 : Fin 2)
    change (R.opB a m).1.1 = (operationB Q a m).trees.1 at h0
    change (R.opB a m).1.2 = (operationB Q a m).trees.2 at h1
    exact Prod.ext h0 h1
  · have hp := (h.2.map (fun p =>
        (RawCpl.relocate a m.c m.lone p.1,RawCpl.relocate a m.c m.lone p.2))).append_right
      ((miniChain m).pairsAt (nodeSign ![1,-1] a) a)
    rw [← raw_opB_pairs R,← raw_opB_pairs Q.raw] at hp
    exact hp.trans (operationB_pairs_perm Q a m ht).symm

/-- Every raw source history produces actual well-formed structure data. -/
theorem RawRegular.exists_wf_rawRep {R : RawCpl} (hR : RawRegular R) :
    ∃ Q : RegCpl, Q.wf = true ∧ RawRep Q R := by
  induction hR with
  | triv => exact ⟨.triv,rfl,rawRep_triv⟩
  | @opA R x y c _ hxy ih =>
    obtain ⟨Q,_,hQ⟩ := ih
    exact ⟨operationA Q x y c,operationA_wf Q x y c,rawRep_opA hQ x y c hxy⟩
  | @opB R a m _ ha ih =>
    obtain ⟨Q,_,hQ⟩ := ih
    exact ⟨operationB Q a m,operationB_wf Q a m,rawRep_opB hQ a m ha⟩

/-- Every source-regular couple lies in the decoding range of well-formed codes. -/
theorem isRegularCouple_exists_wf_decodes (G : Garden 2) (hG : IsRegularCouple G) :
    ∃ Q : RegCpl, Q.wf = true ∧ Q.Decodes G := by
  obtain ⟨R,hR,hmatch⟩ := hG
  obtain ⟨Q,hQ,hrep⟩ := RawRegular.exists_wf_rawRep hR
  exact ⟨Q,hQ,(hrep.decodes_iff G).mpr hmatch⟩

end WaveTurbulence.Reg
