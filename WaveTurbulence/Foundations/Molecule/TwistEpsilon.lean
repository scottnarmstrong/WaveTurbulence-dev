/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistDecorations

/-! # Preservation of the source epsilon coefficient under a unit twist

TARGET defepscoef and Definition twist: conservation at the lower branch
makes the epsilon coefficient invariant under the root/retained exchange.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- Conservation identifies the two equalities used by the epsilon coefficient. -/
theorem lower_equalities {d : ℕ} (a b c : Fin d → ℤ) :
    (c = a-b+c ↔ a = b) ∧ (a = a-b+c ↔ b = c) := by
  constructor
  · constructor
    · intro h
      ext i
      have hi := congrFun h i
      change c i = a i-b i+c i at hi
      omega
    · intro h
      rw [h,sub_self,zero_add]
  · constructor
    · intro h
      ext i
      have hi := congrFun h i
      change a i = a i-b i+c i at hi
      omega
    · intro h
      rw [h,sub_add_cancel]

/-- The lower coefficient is invariant when the retained slot is the left child. -/
theorem epsCoef_exchange_left {d : ℕ} (a b c : Fin d → ℤ) :
    epsCoef (a-b+c) c b = epsCoef a b c := by
  classical
  have h := lower_equalities a b c
  by_cases hab : a = b <;> by_cases hbc : b = c <;>
    simp_all [epsCoef,eq_comm]

/-- The lower coefficient is invariant when the retained slot is the right child. -/
theorem epsCoef_exchange_right {d : ℕ} (a b c : Fin d → ℤ) :
    epsCoef b a (a-b+c) = epsCoef a b c := by
  classical
  have h := lower_equalities a b c
  by_cases hab : a = b <;> by_cases hbc : b = c <;>
    simp_all [epsCoef,eq_comm]

variable {w d : ℕ} (G : Garden w) (P : CorePlacement G)


end WaveTurbulence.Twist
