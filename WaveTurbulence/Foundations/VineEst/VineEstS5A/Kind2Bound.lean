/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5A.PhasePhCph

/-! # An explicit `Cph` for kind-2 blocks (V5 Step 4d-A, item 1)

If the unit intervals of `t₁ⁱ` and `s₁ⁱ` of every kind-2 block differ by at most `g`, then on the time domain
`|t₁ⁱ - s₁ⁱ| ≤ g + 1` and `kind2Factor ≤ (max 1 ((g+1)^(1-3η)))^I`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5A
open WaveTurbulence WaveTurbulence.SumintPar Finset

variable {d : ℕ}

theorem kind2Factor_le_pow (D : SumintPar.SumintDatum d) (η B : ℝ) (τ : D.S.TVar → ℝ) (hB : 0 ≤ B)
    (hτ : ∀ i (h : D.S.nor i = false ∧ D.badKind i = 2 ∧ 0 < D.S.m i),
      |τ (.inl ⟨i, ⟨1, by omega⟩⟩) - τ (.inr (.inl ⟨i, ⟨0, h.2.2⟩⟩))| ≤ B) (hq : 0 ≤ 1 - 3 * η) :
    kind2Factor D η τ ≤ (max 1 (B ^ (1 - 3 * η))) ^ D.S.I := by
  unfold kind2Factor
  calc _ ≤ ∏ _i : Fin D.S.I, (max 1 (B ^ (1 - 3 * η))) := by
        refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
        · split_ifs
          · exact Real.rpow_nonneg (abs_nonneg _) _
          · exact zero_le_one
        · split_ifs with h
          · exact le_max_of_le_right (Real.rpow_le_rpow (abs_nonneg _) (hτ i h) hq)
          · exact le_max_left _ _
    _ = _ := by simp

/-- On the time domain the unit intervals bound the difference of two times. -/
theorem abs_sub_le_of_mem_timeDom (D : SumintPar.SumintDatum d) (hI : 0 < D.S.I) (t t' t'' : ℝ)
    (τ : D.S.TVar → ℝ) (hτ : τ ∈ D.timeDom hI t t' t'') (a b : D.S.TVar) (g : ℝ)
    (hg : |(D.q a : ℝ) - D.q b| ≤ g) : |τ a - τ b| ≤ g + 1 := by
  obtain ⟨h1, -, -⟩ := hτ
  obtain ⟨ha1, ha2, -⟩ := h1 a
  obtain ⟨hb1, hb2, -⟩ := h1 b
  rw [abs_le] at hg ⊢
  constructor <;> linarith [hg.1, hg.2]

end WaveTurbulence.VineEstS5A
