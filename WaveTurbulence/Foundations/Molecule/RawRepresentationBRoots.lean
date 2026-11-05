/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.OperationBRoots

/-! # Source-history induction for mini-tree insertion at either root -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- A source B-step at either original root retains exact raw representation. -/
theorem rawRep_opB_root {Q : RegCpl} {R : RawCpl} (h : RawRep Q R)
    (j : Fin 2) (m : MiniTreeCode) : RawRep (operationB Q (j,[]) m) (R.opB (j,[]) m) := by
  have hfR := raw_opB_update R (j,[]) m
  have hfQ := raw_opB_update Q.raw (j,[]) m
  simp only [h.forest] at hfR
  simp only [raw_tree_eq_coupleForest] at hfQ
  have hf : (R.opB (j,[]) m).tree = coupleForest (operationB Q (j,[]) m) :=
    hfR.trans (hfQ.symm.trans (operationB_root_forest Q j m).symm)
  constructor
  · have h0 := congrFun hf (0 : Fin 2)
    have h1 := congrFun hf (1 : Fin 2)
    change (R.opB (j,[]) m).1.1 = (operationB Q (j,[]) m).trees.1 at h0
    change (R.opB (j,[]) m).1.2 = (operationB Q (j,[]) m).trees.2 at h1
    exact Prod.ext h0 h1
  · have hp := (h.2.map (fun p =>
        (prefixTree j [m.c,m.lone] p.1,prefixTree j [m.c,m.lone] p.2))).append_right
      ((miniChain m).pairsAt (nodeSign ![1,-1] (j,[])) (j,[]))
    have hraw : (R.opB (j,[]) m).2.Perm (Q.raw.opB (j,[]) m).2 := by
      rw [raw_opB_root_pairs,raw_opB_root_pairs]
      exact hp
    exact hraw.trans (operationB_root_pairs_perm Q j m).symm

end WaveTurbulence.Reg
