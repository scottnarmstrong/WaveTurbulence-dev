/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Analysis.Complex.Basic
/-! Finite uniform sums used in leaf derivative identities. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Filter Finset

theorem tendstoUniformly_finset_sum {I X J : Type*} {l : Filter I}
    (S : Finset J) (f : J → I → X → ℂ) (F : J → X → ℂ)
    (h : ∀ j ∈ S, TendstoUniformly (f j) (F j) l) :
    TendstoUniformly (fun i x => ∑ j ∈ S, f j i x) (fun x => ∑ j ∈ S, F j x) l := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    exact Filter.Eventually.of_forall (fun _ _ => by simpa using hε)
  | @insert j S hj ih =>
    have hh := (h j (mem_insert_self j S)).add
      (ih (fun a ha => h a (mem_insert_of_mem ha)))
    have he : (f j + fun i x => ∑ a ∈ S, f a i x) =
        (fun i x => f j i x + ∑ a ∈ S, f a i x) := by funext i x; rfl
    have hF : (F j + fun x => ∑ a ∈ S, F a x) =
        (fun x => F j x + ∑ a ∈ S, F a x) := by funext x; rfl
    rw [he, hF] at hh
    simpa only [sum_insert hj] using hh

end WaveTurbulence.LGSpine
