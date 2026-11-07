/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VineDouble4
/-! The label count of a VC formed by two double bonds, part 5: the cardinality of the triple set. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

namespace DoubleShape

theorem stripSet_card_le (hd : 0 < d) {L τ R βx : ℝ} (hL : 0 < L) (hτ : 0 ≤ τ) (hR : 0 < R) (a : Mom d)
    (nr : Fin d → ℤ) (hnr : R / 2 ≤ ‖latticePoint L nr‖) :
    ((stripSet L τ βx a nr).card : ℝ) ≤
      min ((2 * (L * 2) + 1) ^ (d - 1) * (2 * (d : ℝ) * τ * L / (R / 2) + 1)) (((⌊2 * 2 * L⌋₊ + 1) ^ d : ℕ) : ℝ) := by
  refine le_min ?_ ?_
  · refine WaveTurbulence.CountLemmas.card_dot_strip_ball_norm_le hd (stripSet L τ βx a nr) hL (by norm_num) hτ (by positivity) a
      (latticePoint L nr) (‖latticePoint L nr‖ ^ 2 + βx / 2) hnr ?_ ?_
    · intro n hn
      exact ((Finset.mem_filter.1 hn).2).1
    · intro n hn
      exact ((Finset.mem_filter.1 hn).2).2
  · have : (stripSet L τ βx a nr).card ≤ (alphaN d L a 2).card := Finset.card_filter_le _ _
    exact_mod_cast this.trans (card_alphaN_le L a 2 hL (by norm_num))

theorem tripleFin_card_le (hd : 0 < d) {L τ R ρ βx : ℝ} (hL : 0 < L) (hτ : 0 ≤ τ) (hR : 0 < R) (hρ : 0 ≤ ρ)
    (a1 r₀ a3 : Mom d) :
    ((tripleFin L τ R ρ βx a1 r₀ a3).card : ℝ) ≤
      ((⌊2 * 1 * L⌋₊ + 1) ^ d : ℕ) * ((⌊2 * ρ * L⌋₊ + 1) ^ d : ℕ) *
        min ((2 * (L * 2) + 1) ^ (d - 1) * (2 * (d : ℝ) * τ * L / (R / 2) + 1)) (((⌊2 * 2 * L⌋₊ + 1) ^ d : ℕ) : ℝ) := by
  set B := min ((2 * (L * 2) + 1) ^ (d - 1) * (2 * (d : ℝ) * τ * L / (R / 2) + 1)) (((⌊2 * 2 * L⌋₊ + 1) ^ d : ℕ) : ℝ)
    with hB
  unfold tripleFin
  have h1 : ((((alphaN d L a1 1) ×ˢ ((alphaN d L r₀ ρ).filter fun nr => R / 2 ≤ ‖latticePoint L nr‖)).biUnion
      fun p => (stripSet L τ βx a3 p.2).image fun u => (p.1, p.2, u)).card : ℝ) ≤
      ∑ p ∈ (alphaN d L a1 1) ×ˢ ((alphaN d L r₀ ρ).filter fun nr => R / 2 ≤ ‖latticePoint L nr‖), B := by
    have := Finset.card_biUnion_le (s := (alphaN d L a1 1) ×ˢ ((alphaN d L r₀ ρ).filter fun nr => R / 2 ≤ ‖latticePoint L nr‖))
      (t := fun p => (stripSet L τ βx a3 p.2).image fun u => (p.1, p.2, u))
    refine (Nat.cast_le.2 this).trans ?_
    push_cast
    refine Finset.sum_le_sum fun p hp => ?_
    have hp2 := (Finset.mem_filter.1 (Finset.mem_product.1 hp).2).2
    refine (Nat.cast_le.2 Finset.card_image_le).trans ?_
    exact stripSet_card_le hd hL hτ hR a3 p.2 hp2
  refine h1.trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_product]
  have hA1 := card_alphaN_le L a1 1 hL (by norm_num)
  have hA2 : ((alphaN d L r₀ ρ).filter fun nr => R / 2 ≤ ‖latticePoint L nr‖).card ≤ (⌊2 * ρ * L⌋₊ + 1) ^ d :=
    (Finset.card_filter_le _ _).trans (card_alphaN_le L r₀ ρ hL hρ)
  have hB0 : 0 ≤ B := by
    rw [hB]
    refine le_min (by positivity) (by positivity)
  push_cast
  have : (((alphaN d L a1 1).card : ℝ) * (((alphaN d L r₀ ρ).filter fun nr => R / 2 ≤ ‖latticePoint L nr‖).card : ℝ)) ≤
      ((⌊2 * 1 * L⌋₊ + 1 : ℝ) ^ d) * ((⌊2 * ρ * L⌋₊ + 1 : ℝ) ^ d) := by
    apply mul_le_mul (by exact_mod_cast hA1) (by exact_mod_cast hA2) (by positivity) (by positivity)
  nlinarith [this, hB0]

end DoubleShape
end WaveTurbulence.FinalCount
