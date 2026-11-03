/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.ParityLatticeBound
public import Mathlib.Logic.Equiv.Basic

/-! # Exact product-lattice diagonalization -/

public section
open Finset
open scoped BigOperators
namespace WaveTurbulence.WeylSums

/-- Coordinatewise sum/difference, before imposing parity. -/
@[expose] def pairDiagonalize {d : ℕ} (v : Fin d → ℤ × ℤ) : Fin d → ℤ × ℤ :=
  fun j => ((v j).1+(v j).2,(v j).1-(v j).2)

/-- Exact simultaneous diagonalization in every coordinate. -/
theorem tsum_pair_diagonalize {d : ℕ} (F : (Fin d → ℤ × ℤ) → ℂ) :
    (∑' v : Fin d → ℤ × ℤ, F (pairDiagonalize v)) =
      ∑' v : Fin d → ℤ × ℤ, pairParity (fun _ => 0) v * F v := by
  classical
  let E : (Fin d → ℤ × ℤ) ≃ {v : Fin d → ℤ × ℤ // ∀ j, Even ((v j).1-(v j).2)} :=
    (Equiv.piCongrRight (fun _ : Fin d => bilinearLatticeEquiv)).trans Equiv.subtypePiEquivPi.symm
  have heq : (∑' v : Fin d → ℤ × ℤ, F (pairDiagonalize v)) =
      ∑' v : {v : Fin d → ℤ × ℤ // ∀ j, Even ((v j).1-(v j).2)}, F v.val := by
    exact E.tsum_eq (fun v => F v.val)
  rw [heq]
  have hsub : (∑' v : {v : Fin d → ℤ × ℤ // ∀ j, Even ((v j).1-(v j).2)}, F v.val) =
      ∑' v : Fin d → ℤ × ℤ, {v | ∀ j, Even ((v j).1-(v j).2)}.indicator F v :=
    _root_.tsum_subtype _ F
  rw [hsub]
  apply tsum_congr
  intro v
  by_cases hv : ∀ j, Even ((v j).1-(v j).2)
  · simp [Set.indicator, pairParity, hv]
  · obtain ⟨j,hj⟩ := not_forall.mp hv
    have hz : pairParity (fun _ : Fin d × Fin 2 => 0) v = 0 := by
      apply prod_eq_zero (mem_univ j)
      simp [hj]
    simp [Set.indicator, hv, hz]

end WaveTurbulence.WeylSums
