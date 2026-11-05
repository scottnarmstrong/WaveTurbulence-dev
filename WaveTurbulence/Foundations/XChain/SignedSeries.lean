/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
/-! Root signs preserve finite products and countable decoration sums. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem zpowSign_mul (ζ : ℤˣ) (a b : ℂ) :
    zpowSign ζ (a * b) = zpowSign ζ a * zpowSign ζ b := by
  unfold zpowSign
  split_ifs
  · rfl
  · exact map_mul (starRingEnd ℂ) a b

theorem zpowSign_tsum {α : Type*} (ζ : ℤˣ) (f : α → ℂ) :
    zpowSign ζ (∑' a, f a) = ∑' a, zpowSign ζ (f a) := by
  unfold zpowSign
  split_ifs
  · rfl
  · change star (∑' a, f a) = ∑' a, star (f a)
    exact tsum_star

theorem zpowSign_prod {α : Type*} (ζ : ℤˣ) (s : Finset α) (f : α → ℂ) :
    zpowSign ζ (∏ a ∈ s, f a) = ∏ a ∈ s, zpowSign ζ (f a) := by
  unfold zpowSign
  split_ifs
  · rfl
  · exact map_prod (starRingEnd ℂ) f s

end WaveTurbulence.Induct
