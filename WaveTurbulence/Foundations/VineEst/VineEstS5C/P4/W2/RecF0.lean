/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.FreeRow

/-! # P4-W2 (session 20, step 6A): the rigid factor of a record with its kind

`k2f η i τ`: the kind-2 factor `|t₁ⁱ - s₁ⁱ|^{1-3η}` of the block `i` (`1` when `m i = 0`), the factor of `k2c` at a kind-2 block.  `f0Of η i kd`: the rigid factor of a
record of kind `kd` at the block `i` (`‖r‖` for kind 1, `k2f` for kind 2, `1` otherwise).  `k2c_eq_prod`: `k2c` is the product of the `k2f` over the kind-2 bad blocks. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence

noncomputable def k2f {S : WaveTurbulence.SumintShape} (η : ℝ) (i : Fin S.I) (τ : S.TVar → ℝ) : ℂ :=
  if h : 0 < S.m i then ((|τ (.inl ⟨i, ⟨1, by omega⟩⟩) - τ (.inr (.inl ⟨i, ⟨0, h⟩⟩))| ^ (1 - 3 * η) : ℝ) : ℂ) else 1

open Classical in
noncomputable def f0Of {S : WaveTurbulence.SumintShape} {d : ℕ} (η : ℝ) (i : Fin S.I) (kd : ℕ) :
    (S.TVar → ℝ) → Mom d → ℂ :=
  fun τ rr => if kd = 1 then ((‖rr‖ : ℝ) : ℂ) else if kd = 2 then k2f η i τ else 1

theorem f0Of_of_ne {S : WaveTurbulence.SumintShape} {d : ℕ} (η : ℝ) (i : Fin S.I) {kd : ℕ} (h2 : kd ≠ 2) :
    (f0Of (S := S) (d := d) η i kd) = fun _ rr => if kd = 1 then ((‖rr‖ : ℝ) : ℂ) else 1 := by
  classical
  funext τ rr
  unfold f0Of
  simp [h2]

open Classical in
theorem k2c_eq_prod {S : WaveTurbulence.SumintShape} (bk : Fin S.I → Fin 4) (η : ℝ) (τ : S.TVar → ℝ) :
    k2c bk η τ = ∏ i, (if S.nor i = false ∧ bk i = 2 then k2f η i τ else 1) := by
  unfold k2c
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h1 : S.nor i = false ∧ bk i = 2
  · by_cases h2 : 0 < S.m i
    · rw [dif_pos ⟨h1.1, h1.2, h2⟩, if_pos h1]
      unfold k2f
      rw [dif_pos h2]
    · rw [dif_neg (fun h => h2 h.2.2), if_pos h1]
      unfold k2f
      rw [dif_neg h2]
  · rw [dif_neg (fun h => h1 ⟨h.1, h.2.1⟩), if_neg h1]

end WaveTurbulence.VineEstS5C.P4.W2
