/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepMom1

/-!
# S2 REPRESENTS, VINE-D (moments): the sum over the slot modes of the modulation losses

For a family of slot modes (weights `w s l ≥ 0`, frequencies `m s l`) carrying the moments
`Σ_l ⟨m_{s,l}/2⟩^θ w_{s,l} ≤ μ_s`, the sum over the joint modes `ξ ∈ Π_s Λ_s` of the weights times the unit losses
`Π_j (1 + |λ_j(ξ)|)^c` (`c = 6η⁶`, `2c ≤ θ`, `c ≤ 1`) is at most `Π_s 9 μ_s` (`tsum_modes_moment`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS Finset TTree Reg Reg.Skeleton
open scoped ENNReal

/-- **The lower-slot moment** (R58): the joint sum of the weights times the modulation losses is paid by the slot
moments. -/
theorem tsum_modes_moment {w : ℕ} {G : Garden w} {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J) {Λ : ReplacementSlot G → Type}
    (W : ∀ s, Λ s → ℝ) (hW : ∀ s l, 0 ≤ W s l) (m : ∀ s, Λ s → Fin 2 → ℤ) {c θ : ℝ} (hc : 0 ≤ c)
    (hc1 : c ≤ 1) (hcθ : 2 * c ≤ θ) (μ : ReplacementSlot G → ℝ≥0∞)
    (hμ : ∀ s, ∑' l, maxBracketPow θ (half (m s l)) * ENNReal.ofReal (W s l) ≤ μ s) :
    ∑' ξ : ∀ s, Λ s, ENNReal.ofReal ((∏ s, W s (ξ s)) *
      ∏ j, (1 + |((modLam (fun s => m s (ξ s)) route j : ℤ) : ℝ)|) ^ c) ≤ ∏ s, (9 * μ s) := by
  classical
  have h1 : ∀ ξ : ∀ s, Λ s, ENNReal.ofReal ((∏ s, W s (ξ s)) *
      ∏ j, (1 + |((modLam (fun s => m s (ξ s)) route j : ℤ) : ℝ)|) ^ c) ≤
      ∏ s, (9 * (maxBracketPow θ (half (m s (ξ s))) * ENNReal.ofReal (W s (ξ s)))) := by
    intro ξ
    have hb := prod_modLam_le (fun s => m s (ξ s)) route hc
    have hp : 0 ≤ ∏ s, W s (ξ s) := Finset.prod_nonneg fun s _ => hW s _
    calc ENNReal.ofReal ((∏ s, W s (ξ s)) * ∏ j, (1 + |((modLam (fun s => m s (ξ s)) route j : ℤ) : ℝ)|) ^ c)
        ≤ ENNReal.ofReal ((∏ s, W s (ξ s)) * ∏ s, ∏ i, (1 + |((m s (ξ s) i : ℤ) : ℝ)|) ^ c) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hb hp)
      _ = ENNReal.ofReal (∏ s, (W s (ξ s) * ∏ i, (1 + |((m s (ξ s) i : ℤ) : ℝ)|) ^ c)) := by
          rw [Finset.prod_mul_distrib]
      _ = ∏ s, ENNReal.ofReal (W s (ξ s) * ∏ i, (1 + |((m s (ξ s) i : ℤ) : ℝ)|) ^ c) :=
          ENNReal.ofReal_prod_of_nonneg fun s _ => mul_nonneg (hW s _)
            (Finset.prod_nonneg fun i _ => by positivity)
      _ ≤ _ := by
          refine Finset.prod_le_prod fun s _ => ?_
          rw [ENNReal.ofReal_mul (hW s _)]
          calc ENNReal.ofReal (W s (ξ s)) * ENNReal.ofReal (∏ i, (1 + |((m s (ξ s) i : ℤ) : ℝ)|) ^ c)
              ≤ ENNReal.ofReal (W s (ξ s)) * (9 * maxBracketPow θ (half (m s (ξ s)))) :=
                by gcongr; exact prod_one_add_abs_le_maxBracketPow _ hc hc1 hcθ
            _ = _ := by ring
  calc _ ≤ ∑' ξ : ∀ s, Λ s, ∏ s, (9 * (maxBracketPow θ (half (m s (ξ s))) * ENNReal.ofReal (W s (ξ s)))) :=
        ENNReal.tsum_le_tsum h1
    _ = ∏ s, ∑' l, 9 * (maxBracketPow θ (half (m s l)) * ENNReal.ofReal (W s l)) :=
        ennreal_tsum_pi_prod_fintype (fun s l => 9 * (maxBracketPow θ (half (m s l)) * ENNReal.ofReal (W s l)))
    _ ≤ _ := by
        refine Finset.prod_le_prod fun s _ => ?_
        rw [ENNReal.tsum_mul_left]
        gcongr; exact hμ s

end WaveTurbulence.Represents
