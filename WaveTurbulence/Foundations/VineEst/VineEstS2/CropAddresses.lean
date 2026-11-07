/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CropTree

/-! # Exact branching addresses of the cropped source tree -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree

/-- Every branching ancestor on the route to a retained address is kept. -/
def RouteKept : (Path → Bool) → Path → Prop
  | keep,[] => keep [] = true
  | keep,i::p => keep [] = true ∧ RouteKept (fun q => keep (i::q)) p

theorem cropTree_branching_iff (T : TTree) (keep : Path → Bool) (p : Path) :
    p ∈ (cropTree T keep).branching ↔ p ∈ T.branching ∧ RouteKept keep p := by
  induction T generalizing keep p with
  | leaf => simp only [cropTree,branching,Finset.notMem_empty,false_and]
  | node l m r hl hm hr =>
    by_cases hk : keep [] = true
    · cases p with
      | nil => simp only [cropTree,hk,ite_true,branching,Finset.mem_insert_self,RouteKept,and_self]
      | cons i p =>
        have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi with rfl | rfl | rfl
        · simpa only [cropTree,hk,ite_true,branching,RouteKept,true_and,cons_mem_pre,
            Finset.mem_insert,Finset.mem_union,List.cons_ne_nil,Fin.reduceEq,and_true,and_false,
            false_and,false_or,or_false,true_or] using hl (fun q => keep (0::q)) p
        · simpa only [cropTree,hk,ite_true,branching,RouteKept,true_and,cons_mem_pre,
            Finset.mem_insert,Finset.mem_union,List.cons_ne_nil,Fin.reduceEq,and_true,and_false,
            false_and,false_or,or_false,true_or] using hm (fun q => keep (1::q)) p
        · simpa only [cropTree,hk,ite_true,branching,RouteKept,true_and,cons_mem_pre,
            Finset.mem_insert,Finset.mem_union,List.cons_ne_nil,Fin.reduceEq,and_true,and_false,
            false_and,false_or,or_false,true_or] using hr (fun q => keep (2::q)) p
    · cases p <;> simp only [cropTree,hk,Bool.false_eq_true,ite_false,branching,
        Finset.notMem_empty,RouteKept,false_and,and_false]

end WaveTurbulence.VineEstS2
