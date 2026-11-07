/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5A.Kind2Bound
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ScaledSumint

/-! # P2: the kind-2 phase bound `hCph` (4d-A item (ii))

`hCph_of_q`: if for every kind-2 block `i` the unit intervals of `t₁ⁱ` and `s₁ⁱ` differ by at most `g`
(`g = 1` when `L_{u3} - L_{u4} ≤ 1`; for a difference `≥ 2` the insertion is trivial, TARGET L1927), then on the time
domain `kind2Factor D η τ ≤ (max 1 ((g+1)^(1-3η)))^I`, with `kind2Factor_le_pow` and `abs_sub_le_of_mem_timeDom`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A

variable {d : ℕ}

/-- The constant `Cph` of the kind-2 phase. -/
noncomputable def cphConst (D : SumintPar.SumintDatum d) (η g : ℝ) : ℝ := (max 1 ((g + 1) ^ (1 - 3 * η))) ^ D.S.I

theorem cphConst_nonneg (D : SumintPar.SumintDatum d) (η g : ℝ) : 0 ≤ cphConst D η g :=
  pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _

/-- `hCph` of the engine from the unit-interval hypothesis on the kind-2 blocks. -/
theorem hCph_of_q (D : SumintPar.SumintDatum d) (hI : 0 < D.S.I) (η g : ℝ) (hg : 0 ≤ g) (hq : 0 ≤ 1 - 3 * η)
    (hqq : ∀ i (h : D.S.nor i = false ∧ D.badKind i = 2 ∧ 0 < D.S.m i),
      |((D.q (.inl ⟨i, ⟨1, by omega⟩⟩) : ℕ) : ℝ) - ((D.q (.inr (.inl ⟨i, ⟨0, h.2.2⟩⟩)) : ℕ) : ℝ)| ≤ g) :
    ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), kind2Factor D η τ ≤ cphConst D η g := by
  intro tt _ τ hτ
  refine kind2Factor_le_pow D η (g + 1) τ (by linarith) (fun i h => ?_) hq
  exact abs_sub_le_of_mem_timeDom D hI _ _ _ τ hτ _ _ g (hqq i h)

end WaveTurbulence.VineEstS5C.P2
