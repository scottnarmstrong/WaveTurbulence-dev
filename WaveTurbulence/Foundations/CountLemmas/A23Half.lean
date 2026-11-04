/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.CountLemmas.A23HalfCyclic
public import WaveTurbulence.Foundations.CountLemmas.A23HalfAnti

/-!
# DH23 Lemma A.2(3), `γ > 1/2` branch, with the explicit saving `κ(γ) = min((2γ−1)/3, 1−γ)`

DH23 (`Revision_Submit.tex`) L2050–L2091, (countc2-1) second line; the referee's proof
(`docs/research/case4-gamma-above-half-referee.txt`, item 4, §4.3); FINDINGS F75.

For the coupled-triple set `𝒞₂` of DH23 (basiccount02) — the landed `coupledTripleSet`, the second counting set of
`countLemma_bound` — and **every** selector `ζ ∈ {x − v, x + y − v, x + y − v − z}`:

`#𝒞₂ ≤ C δ⁻² (1 + log L)² L^{3(d−γ) − γ₀ − κ(γ)}`,   `γ₀ = 1 − γ`, for `1/2 < γ < 1`.

The landed `countLemma_bound` gives the exponent `3(d−γ) − γ₀`; the saving `κ(γ)` replaces DH23's `10η` (so the
statement does not depend on `η`; DH23's `L^{-10η}` follows for `20η ≤ κ(γ)`). `C` is independent of `δ`; `L₀` depends
on `δ`.

* `ζ = x + y − v − z` (cyclic) and `ζ = x + y − v`: `coupledTriple_sum_bound_half`, saving `(2γ−1)/3`;
* `ζ = x − v` (anti-parallel): `coupledTriple_star_bound_half`, saving `κ(γ)`.
-/

public section

open Set

namespace WaveTurbulence.CountLemmas

/-- **DH23 Lemma A.2(3), `γ > 1/2`: `#𝒞₂ ≲ δ⁻² (log L)² L^{3(d−γ) − γ₀ − κ(γ)}` for all three selectors.** -/
theorem a23Half_bound :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (1 / 2 : ℝ) 1 → ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1,
      ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ ax ay az : Mom d, ∀ nv : Fin d → ℤ, ∀ α β : ℝ, ∀ ζsel : Fin 3,
        ((coupledTripleSet L ax ay az (latticePoint L nv) α β (δ⁻¹ * L ^ (-2 * γ)) ζsel).ncard : ℝ) ≤
          C * δ⁻¹ ^ 2 * (1 + Real.log L) ^ 2 * L ^ (3 * ((d : ℝ) - γ) - (1 - γ) - kappaHalf γ) := by
  intro d hd γ hγ
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 3 := ⟨d - 3, by omega⟩
  obtain ⟨C₁, hC₁, hstar⟩ := coupledTriple_star_bound_half n γ hγ
  obtain ⟨C₂, L₂, hC₂, hsum⟩ := coupledTriple_sum_bound_half (n + 3) hd γ ⟨hγ.1.le, hγ.2.le⟩
  refine ⟨C₁ + C₂, by positivity, fun δ hδ => ?_⟩
  obtain ⟨L₁, hL₁⟩ := hstar δ hδ
  refine ⟨max (max L₁ L₂) 1, fun L hL ax ay az nv α β ζsel => ?_⟩
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hLL₁ : L₁ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLL₂ : L₂ ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ.1).mpr hδ.2
  have hlg : 1 ≤ (1 + Real.log L) ^ 2 := one_le_pow₀ (by linarith only [Real.log_nonneg hL1])
  have hpos : 0 ≤ δ⁻¹ ^ 2 * (1 + Real.log L) ^ 2 * L ^ (3 * (((n + 3 : ℕ) : ℝ) - γ) - (1 - γ) - kappaHalf γ) := by
    positivity
  -- the sum selectors, with the larger saving `(2γ−1)/3`
  have hsel : ∀ sel : Bool,
      ((coupledTripleSet L ax ay az (latticePoint L nv) α β (δ⁻¹ * L ^ (-2 * γ)) (if sel then 2 else 1)).ncard : ℝ) ≤
        (C₁ + C₂) * δ⁻¹ ^ 2 * (1 + Real.log L) ^ 2 *
          L ^ (3 * (((n + 3 : ℕ) : ℝ) - γ) - (1 - γ) - kappaHalf γ) := by
    intro sel
    refine (hsum L hLL₂ δ hδ ax ay az nv sel α β).trans ?_
    have hexp : L ^ (3 * (((n + 3 : ℕ) : ℝ) - γ) - (1 - γ) - (2 * γ - 1) / 3) ≤
        L ^ (3 * (((n + 3 : ℕ) : ℝ) - γ) - (1 - γ) - kappaHalf γ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [kappaHalf_le_third γ])
    calc C₂ * δ⁻¹ ^ 2 * L ^ (3 * (((n + 3 : ℕ) : ℝ) - γ) - (1 - γ) - (2 * γ - 1) / 3)
        ≤ C₂ * (δ⁻¹ ^ 2 * (1 + Real.log L) ^ 2 * L ^ (3 * (((n + 3 : ℕ) : ℝ) - γ) - (1 - γ) - kappaHalf γ)) := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hC₂.le
          calc δ⁻¹ ^ 2 * L ^ (3 * (((n + 3 : ℕ) : ℝ) - γ) - (1 - γ) - (2 * γ - 1) / 3)
              ≤ δ⁻¹ ^ 2 * L ^ (3 * (((n + 3 : ℕ) : ℝ) - γ) - (1 - γ) - kappaHalf γ) := by gcongr
            _ ≤ δ⁻¹ ^ 2 * (1 + Real.log L) ^ 2 *
                L ^ (3 * (((n + 3 : ℕ) : ℝ) - γ) - (1 - γ) - kappaHalf γ) := by
                have h := mul_le_mul_of_nonneg_left
                  (le_mul_of_one_le_left (Real.rpow_nonneg (by linarith only [hL1])
                    (3 * (((n + 3 : ℕ) : ℝ) - γ) - (1 - γ) - kappaHalf γ)) hlg)
                  (by positivity : (0 : ℝ) ≤ δ⁻¹ ^ 2)
                simpa only [mul_assoc] using h
      _ ≤ _ := by nlinarith [hC₁, hpos]
  fin_cases ζsel
  · refine (hL₁ L hLL₁ ax ay az nv α β).trans ?_
    have : C₁ * δ⁻¹ ^ 2 * (1 + Real.log L) ^ 2 * L ^ (3 * (((n + 3 : ℕ) : ℝ) - γ) - (1 - γ) - kappaHalf γ) =
        C₁ * (δ⁻¹ ^ 2 * (1 + Real.log L) ^ 2 * L ^ (3 * (((n + 3 : ℕ) : ℝ) - γ) - (1 - γ) - kappaHalf γ)) := by ring
    rw [this]
    nlinarith [hC₂, hpos]
  · exact hsel false
  · exact hsel true

end WaveTurbulence.CountLemmas
