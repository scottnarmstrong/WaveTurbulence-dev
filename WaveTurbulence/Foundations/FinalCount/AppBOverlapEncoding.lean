/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBOverlapOrder
import Mathlib.Tactic

/-! # Exact label encodings for the finite overlap ordering -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole

/-- The first chosen group is the first original group unless the source
atoms are exchanged. -/
theorem appb_overlap_first_index (σ τ : Fin 3 → ℤˣ) (o : AppbOverlapOrder σ τ) (j : Fin 3) :
    appbOverlapRaw false o.swap (o.first j) = o.index (![0,1,2] j) := by
  have hh := o.first_indices j
  cases hs : o.swap <;> simpa [appbOverlapRaw,hs] using hh

theorem appb_overlap_second_index (σ τ : Fin 3 → ℤˣ) (o : AppbOverlapOrder σ τ) (j : Fin 3) :
    appbOverlapRaw false (!o.swap) (o.second j) = o.index
      (![ (appbStarSecond o.profile (fun i : Fin 5 => i)).1,
        (appbStarSecond o.profile (fun i : Fin 5 => i)).2.1,
        (appbStarSecond o.profile (fun i : Fin 5 => i)).2.2] j) := by
  have hh := o.second_indices j
  cases hs : o.swap <;> simpa [appbOverlapRaw,hs] using hh

theorem appb_overlap_first_encoding {K : Type*} (σ τ : Fin 3 → ℤˣ) (o : AppbOverlapOrder σ τ)
    (q : Fin 5 → K) (j : Fin 3) :
    q (appbOverlapRaw false o.swap (o.first j)) = q (o.index (![0,1,2] j)) :=
  congrArg q (appb_overlap_first_index σ τ o j)

theorem appb_overlap_second_encoding {K : Type*} (σ τ : Fin 3 → ℤˣ) (o : AppbOverlapOrder σ τ)
    (q : Fin 5 → K) :
    appbStarSecond o.profile (fun i => q (o.index i)) =
      (q (appbOverlapRaw false (!o.swap) (o.second 0)),
        q (appbOverlapRaw false (!o.swap) (o.second 1)),
        q (appbOverlapRaw false (!o.swap) (o.second 2))) := by
  rw [appb_overlap_second_index σ τ o 0,appb_overlap_second_index σ τ o 1,appb_overlap_second_index σ τ o 2]
  generalize o.profile = ζ
  fin_cases ζ <;> rfl

end WaveTurbulence.Mole
