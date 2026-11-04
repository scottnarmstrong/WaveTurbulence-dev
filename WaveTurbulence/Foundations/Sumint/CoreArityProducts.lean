/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceCoreArity
public import WaveTurbulence.Foundations.Sumint.FiberBigOperators

/-!
# Exact counting products within a source core

The old factor arities add to the unchanged coarse coordinate count.
Consequently multiplying lattice counting powers incurs exactly the
coarse input count, including zero-dimensional unused labels.
-/

public section
open scoped BigOperators Classical
namespace WaveTurbulence.Sumint

/-- The old arities in one source core sum to its literal coordinate count. -/
theorem sum_factorArity_sourceCore {d : ℕ} (D : SumintDatum d) (b : FactorIdx D.S) :
    (∑ a : {a : FactorIdx D.S // sourceCoreGroup D a = b}, factorArity D.S a.1) =
      sourceCoreArity D b := by
  have hc := Fintype.card_sigma (α := fun a : {a : FactorIdx D.S // sourceCoreGroup D a = b} => FactorCoordinate D.S a.1)
  have he : Fintype.card (Σ a : {a : FactorIdx D.S // sourceCoreGroup D a = b}, FactorCoordinate D.S a.1) = sourceCoreArity D b :=
    Fintype.card_congr (Equiv.refl _)
  rw [← he]
  simpa only [card_factorCoordinate] using hc.symm

/-- A core's lattice counting powers retain exactly its input arity. -/
theorem prod_counting_sourceCore {d : ℕ} (D : SumintDatum d) (b : FactorIdx D.S) (Q : ℝ) :
    (∏ a : {a : FactorIdx D.S // sourceCoreGroup D a = b}, Q^(d*factorArity D.S a.1)) =
      Q^(d*sourceCoreArity D b) := by
  rw [Finset.prod_pow_eq_pow_sum,← Finset.mul_sum,sum_factorArity_sourceCore]

end WaveTurbulence.Sumint
