/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TopLeafGroups
/-! The balanced nonempty blocks surviving gauge symmetry have even size at least two. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem even_card_of_balanced_units {ι : Type*} (ζ : ι → ℤˣ) (s : Finset ι)
    (hs : (∑ j ∈ s, (ζ j : ℤ)) = 0) : Even s.card := by
  have hz : ((∑ j ∈ s, (ζ j : ℤ) : ℤ) : ZMod 2) = 0 := by rw [hs]; rfl
  have hone (j : ι) : ((ζ j : ℤ) : ZMod 2) = 1 := by
    rcases Int.units_eq_one_or (ζ j) with h | h <;> rw [h] <;> decide
  have he : (s.card : ZMod 2) = 0 := by
    simpa only [Int.cast_sum, hone, Finset.sum_const, nsmul_eq_mul, mul_one] using hz
  exact (ZMod.natCast_eq_zero_iff_even).mp he

end WaveTurbulence.Induct
