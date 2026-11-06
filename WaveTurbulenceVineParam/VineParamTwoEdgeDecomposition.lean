/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamGraphSplice
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! # Exact finite-sum decomposition at the two source cut occurrences -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {β A : Type*} [Fintype β] [DecidableEq β] [AddCommMonoid A]

/-- Every old bond sum consists of the uncut occurrences and the two actual
cut occurrences. Parallel bonds stay distinct because i and j are indices. -/
theorem sum_two_edge_rest (i j : β) (hij : i ≠ j) (f : β → A) :
    (∑ e,f e)=(∑ e : {e : β // e ≠ i ∧ e ≠ j},f e.1)+f i+f j := by
  have hs : ∀ e,e ∈ (univ : Finset β) \ {i,j} ↔ e ≠ i ∧ e ≠ j := by
    intro e
    simp only [mem_sdiff,mem_univ,true_and,mem_insert,mem_singleton,not_or]
  have hh := Finset.sum_sdiff (f := f) (show ({i,j} : Finset β) ⊆ univ from subset_univ _)
  rw [Finset.sum_subtype _ hs f,sum_pair hij] at hh
  simpa only [add_assoc] using hh.symm

end WaveTurbulence.Vine.Param
