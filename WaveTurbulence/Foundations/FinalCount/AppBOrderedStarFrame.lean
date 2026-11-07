/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBOverlapOrder
public import WaveTurbulence.Foundations.FinalCount.AppBStarFrame
public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrameReindex
import Mathlib.Tactic

/-! # Building canonical star frames from the two actual triple supports -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbOrderedStarFrame {M : Molecule V D} {P : AppbPattern} {r : AppbRealization M P}
    {v1 v2 : V} (e : Fin 5 ↪ Fin P.edges.length) (t1 : AppbTripleFrame r v1) (t2 : AppbTripleFrame r v2)
    (h1 : ∀ j,t1.index j = e (![0,1,2] j)) (h2 : ∀ j,t2.index j = e (![0,3,4] j))
    (o : AppbOverlapOrder (fun j => appbIncidenceSign M v1 (r.edge (t1.index j)).val)
      (fun j => appbIncidenceSign M v2 (r.edge (t2.index j)).val)) :
    AppbStarFrame r (if o.swap then v2 else v1) (if o.swap then v1 else v2) := by
  cases ho : o.swap
  · refine {
      index := o.index.trans e, profile := o.profile,
      first := t1.reindex o.first, second := t2.reindex o.second,
      first_indices := ?_, second_indices := ?_,
      first_same := ?_, first_opposite := ?_, second_same := ?_, second_opposite := ?_ }
    · intro j
      change t1.index (o.first j) = e (o.index (![0,1,2] j))
      rw [h1]
      exact congrArg e (by simpa [appbOverlapRaw,ho] using o.first_indices j)
    · intro j
      change t2.index (o.second j) = e (o.index _)
      rw [h2]
      exact congrArg e (by simpa [appbOverlapRaw,ho] using o.second_indices j)
    · simpa only [ho,Bool.false_eq_true,ite_false,AppbTripleFrame.reindex,Function.Embedding.trans_apply,Equiv.coe_toEmbedding] using o.first_same
    · simpa only [ho,Bool.false_eq_true,ite_false,AppbTripleFrame.reindex,Function.Embedding.trans_apply,Equiv.coe_toEmbedding] using o.first_opposite
    · simpa only [ho,Bool.false_eq_true,ite_false,AppbTripleFrame.reindex,Function.Embedding.trans_apply,Equiv.coe_toEmbedding] using o.second_same
    · simpa only [ho,Bool.false_eq_true,ite_false,AppbTripleFrame.reindex,Function.Embedding.trans_apply,Equiv.coe_toEmbedding] using o.second_opposite
  · refine {
      index := o.index.trans e, profile := o.profile,
      first := t2.reindex o.first, second := t1.reindex o.second,
      first_indices := ?_, second_indices := ?_,
      first_same := ?_, first_opposite := ?_, second_same := ?_, second_opposite := ?_ }
    · intro j
      change t2.index (o.first j) = e (o.index (![0,1,2] j))
      rw [h2]
      exact congrArg e (by simpa [appbOverlapRaw,ho] using o.first_indices j)
    · intro j
      change t1.index (o.second j) = e (o.index _)
      rw [h1]
      exact congrArg e (by simpa [appbOverlapRaw,ho] using o.second_indices j)
    · simpa only [ho,ite_true,AppbTripleFrame.reindex,Function.Embedding.trans_apply,Equiv.coe_toEmbedding] using o.first_same
    · simpa only [ho,ite_true,AppbTripleFrame.reindex,Function.Embedding.trans_apply,Equiv.coe_toEmbedding] using o.first_opposite
    · simpa only [ho,ite_true,AppbTripleFrame.reindex,Function.Embedding.trans_apply,Equiv.coe_toEmbedding] using o.second_same
    · simpa only [ho,ite_true,AppbTripleFrame.reindex,Function.Embedding.trans_apply,Equiv.coe_toEmbedding] using o.second_opposite

end WaveTurbulence.Mole
