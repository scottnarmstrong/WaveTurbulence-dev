/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceFactorTrivial
public import WaveTurbulence.Foundations.Sumint.TimeFactorCoordinates

/-!
# Counting independent source inputs and fixed-time losses

The total arity is precisely M. Fixing two input-time coordinates can
hit at most two independent factors, whose combined arity is at most
six. These are the input counts used in the positive Fourier endpoint.
-/

public section

namespace WaveTurbulence.Sumint

/-- The coordinate cardinality is exactly the factor arity. -/
theorem card_factorCoordinate (S : SumintShape) (a : FactorIdx S) :
    Fintype.card (FactorCoordinate S a) = factorArity S a := by
  rcases a with i | (p | i) <;> rfl

end WaveTurbulence.Sumint
