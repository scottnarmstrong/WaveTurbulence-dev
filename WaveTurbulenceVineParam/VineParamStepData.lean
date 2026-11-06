/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamContractStep
public import WaveTurbulenceVineParam.VineParamExpandSym
public import WaveTurbulenceVineParam.VineParamSkipEquiv
import Mathlib.Tactic

/-! # Cap reflection on `Fin n` and the relabeled rest of a contraction -/

public section
namespace WaveTurbulence.Vine.Param
open Finset

/-- An involutive-style label permutation preserving a cap and fixing its complement,
restricted to the labels below `n`. -/
@[expose] def reflFinGen (ν : ℕ ≃ ℕ) (Cn : Finset ℕ) (N n : ℕ) (hCold : ∀ t ∈ Cn,t < N) (hn : N ≤ n)
    (hνout : ∀ t ∉ Cn,ν t = t) (hνmem : ∀ t,ν t ∈ Cn ↔ t ∈ Cn) : Fin n ≃ Fin n where
  toFun t := ⟨ν t.1,by
    by_cases ht : t.1 ∈ Cn
    · have := hCold _ ((hνmem t.1).mpr ht); omega
    · rw [hνout _ ht]; exact t.2⟩
  invFun t := ⟨ν.symm t.1,by
    by_cases ht : t.1 ∈ Cn
    · have h2 : ν.symm t.1 ∈ Cn := by
        have := hνmem (ν.symm t.1)
        rw [ν.apply_symm_apply] at this
        exact this.mp ht
      have := hCold _ h2; omega
    · have h2 : ν t.1 = t.1 := hνout _ ht
      have : ν.symm t.1 = t.1 := by rw [ν.symm_apply_eq]; exact h2.symm
      rw [this]; exact t.2⟩
  left_inv t := by apply Fin.ext; simp
  right_inv t := by apply Fin.ext; simp

theorem reflFinGen_apply (ν : ℕ ≃ ℕ) (Cn : Finset ℕ) (N n : ℕ) (hCold hn hνout hνmem)
    (t : Fin n) : (reflFinGen ν Cn N n hCold hn hνout hνmem t).1 = ν t.1 := rfl

theorem reflFinGen_symm_apply (ν : ℕ ≃ ℕ) (Cn : Finset ℕ) (N n : ℕ) (hCold hn hνout hνmem)
    (t : Fin n) : ((reflFinGen ν Cn N n hCold hn hνout hνmem).symm t).1 = ν.symm t.1 := rfl

end WaveTurbulence.Vine.Param
