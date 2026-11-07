/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.Data

/-!
# The literal source output-time set lies in the step cube

Only the drafted unit-interval containment hypothesis is used. The
strict output-time ordering is retained exactly in the set definition.
-/

@[expose] public section
set_option autoImplicit false
open Set
namespace WaveTurbulence.SumintPar

/-- The exact output-time set in the drafted source proposition. -/
@[expose] def sourceOutputTimeSet {d : ℕ} (D : SumintDatum d) : Set (Fin 3 → ℝ) :=
  {t | (∀ j, (D.qOut j:ℝ) ≤ t j ∧ t j ≤ D.qOut j+1) ∧ max (t 1) (t 2) < t 0}

/-- Every source output-time point lies in the full cube on which the ambient extension agrees. -/
theorem sourceOutputTimeSet_subset_cube {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hD : D.Admissible A L γ η N)
    {t : Fin 3 → ℝ} (ht : t ∈ sourceOutputTimeSet D) (j : Fin 3) : t j ∈ Icc (0:ℝ) N := by
  have hq : D.qOut j+1 ≤ N := hD.2.2.2.2.2.2.2.2.1 j
  refine ⟨(Nat.cast_nonneg _).trans (ht.1 j).1,(ht.1 j).2.trans ?_⟩
  exact_mod_cast hq

end WaveTurbulence.SumintPar
