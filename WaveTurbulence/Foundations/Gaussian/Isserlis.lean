/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Gaussian.IsserlisMoments
public import WaveTurbulence.Foundations.Gaussian.IsserlisPairings
public import WaveTurbulence.Foundations.Gaussian.IsserlisPartitions

/-!
# Complex Isserlis formula

DH21 Lemma A.2, expressed as a sum over bijections from positive positions to
negative positions. Each positive position specifies one unordered pair.
-/

public section

open MeasureTheory ProbabilityTheory
open WaveTurbulence.GaussianPairings
open scoped Classical

namespace WaveTurbulence

/-- Complex Isserlis formula, DH21 Lemma A.2. Repeated indices are permitted.
A pairing is a bijection from positive positions to negative positions; its
weight is the product of equality indicators on the paired Gaussian indices. -/
theorem integral_signed_prod_eq_sum_pairings {Ω J ι : Type*} [MeasurableSpace Ω]
    [DecidableEq J] [DecidableEq ι] {P : Measure Ω} {η : ι → Ω → ℂ}
    (hη : iIndepFun η P) (hlaw : ∀ i, HasLaw (η i) stdComplexGaussian P)
    (s : Finset J) (k : J → ι) (ζ : J → Bool) :
    (∫ ω, ∏ j ∈ s, if ζ j then η (k j) ω else star (η (k j) ω) ∂P) =
      ∑ e : SignedPairing s ζ,
        ∏ a : SignedPositions s ζ true,
          if k a.1 = k (e a).1 then (1 : ℂ) else 0 := by
  have hsum := sum_equiv_weight (positionLabel s k ζ true) (positionLabel s k ζ false)
  have hcount := card_compatible_signedPairing s k ζ
  have he (e : SignedPairing s ζ) (a : SignedPositions s ζ true) :
      positionLabel s k ζ false (e a) = positionLabel s k ζ true a ↔
        k a.1 = k (e a).1 :=
    ⟨fun h => (congrArg Subtype.val h).symm, fun h => Subtype.ext h.symm⟩
  rw [integral_signed_prod_eq_prod_factorial hη hlaw]
  calc
    _ = (Nat.card {e : SignedPairing s ζ // ∀ a,
        positionLabel s k ζ false (e a) = positionLabel s k ζ true a} : ℂ) := by
      rw [hcount]
      push_cast
      rfl
    _ = _ := by
      rw [← hsum]
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.prod_congr rfl
      intro a _
      rw [he]
      split_ifs <;> norm_num

end WaveTurbulence
