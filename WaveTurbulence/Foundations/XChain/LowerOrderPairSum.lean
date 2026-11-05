/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LowerOrderKernelSum
public import WaveTurbulence.Foundations.XChain.LowerPairKernelSum
/-! Two-point attached components have order zero; unbalanced ordered components are empty. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem lowerOrderKernelSum_pair {d p Natt : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin 2 → ℤˣ) (N : Fin (Natt + 1)) (n : Fin 2 → (Fin d → ℤ)) :
    lowerOrderKernelSum L γ δ F sig p Natt N n =
      if N.1 = 0 then lowerKernelSum L γ δ F sig p Natt n else 0 := by
  classical
  have ho (D : LowerGraftData sig p Natt) : D.low.garden.order = 0 :=
    leafForest_garden_order _ D.leafPair.1
  unfold lowerOrderKernelSum
  simp_rw [ho]
  by_cases hN : N.1 = 0
  · simp only [hN, ite_true]
    rfl
  · simp only [Ne.symm hN, hN, ite_false, sum_const_zero]

theorem lowerOrderKernelSum_unbalanced {w d p Natt : ℕ} (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) (sig : Fin w → ℤˣ) (N : Fin (Natt + 1))
    (hs : ∑ j, (sig j : ℤ) ≠ 0) (n : Fin w → (Fin d → ℤ)) :
    lowerOrderKernelSum L γ δ F sig p Natt N n = 0 := by
  haveI : IsEmpty (LowerGraftData sig p Natt) := ⟨fun D => hs (by
    rw [← D.sign]
    exact SysAPI.Garden.sum_sig_eq_zero D.low.garden D.plain)⟩
  simp only [lowerOrderKernelSum, Finset.univ_eq_empty, sum_empty]

end WaveTurbulence.Induct
