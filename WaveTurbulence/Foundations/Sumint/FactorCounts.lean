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

/-- Every factor carries between one and three input coordinates. -/
theorem factorArity_bounds (S : SumintShape) (a : FactorIdx S) :
    1 ≤ factorArity S a ∧ factorArity S a ≤ 3 := by
  rcases a with i | (p | i) <;> simp only [factorArity] <;> omega

/-- The coordinate cardinality is exactly the factor arity. -/
theorem card_factorCoordinate (S : SumintShape) (a : FactorIdx S) :
    Fintype.card (FactorCoordinate S a) = factorArity S a := by
  rcases a with i | (p | i) <;> rfl

/-- The exact source number M is the sum of all factor arities. -/
theorem sum_factorArity (S : SumintShape) :
    ∑ a : FactorIdx S, factorArity S a = S.M := by
  have hc : Fintype.card (Σ a : FactorIdx S, FactorCoordinate S a) = S.M :=
    (Fintype.card_congr (factorCoordinateTimeEquiv S)).trans (card_time_index S)
  simpa only [Fintype.card_sigma,card_factorCoordinate] using hc

/-- The total arity of any selected factor family is at most three times its size. -/
theorem sum_factorArity_le (S : SumintShape) (s : Finset (FactorIdx S)) :
    ∑ a ∈ s, factorArity S a ≤ 3*s.card := by
  calc
    _ ≤ ∑ _a ∈ s, 3 := Finset.sum_le_sum (fun a _ => (factorArity_bounds S a).2)
    _ = _ := by simp [Nat.mul_comm]

/-- The factors affected by a given finite set of fixed source input times. -/
@[expose] noncomputable def exitFactors (S : SumintShape) (s : Finset S.TVar) :
    Finset (FactorIdx S) := by
  classical
  exact s.image (fun v => (timeFactorCoordinate S v).1)

/-- Fixing at most two times affects no more than six momentum inputs. -/
theorem sum_arity_exitFactors_le_six (S : SumintShape) (s : Finset S.TVar)
    (hs : s.card ≤ 2) :
    ∑ a ∈ exitFactors S s, factorArity S a ≤ 6 := by
  have hc : (exitFactors S s).card ≤ s.card := Finset.card_image_le
  exact (sum_factorArity_le S _).trans (by omega)

end WaveTurbulence.Sumint
