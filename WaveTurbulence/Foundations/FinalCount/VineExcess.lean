/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VineArith
public import WaveTurbulence.Foundations.FinalCount.VineRank2
public import WaveTurbulence.Foundations.FinalCount.Prop94Iota
/-! Vine removal, part 8 (FINALCOUNT-G2): DH23 Prop 9.4, Step 1, single vine (L1797--L1801), **conditional on the
label count `𝔉`** (`VineLabelBound`, the named obligation of L1799--L1801).

`vine_excess_single`: if the number of label vectors of the removed vine is `≤ 𝔉 =
Cf · L^d (ρL)^d · L^{(m-2)(d-γ)} δ^{-m/2} (log L)^e / ∏_{ladders ⊂ VC} 𝔛^z` (the display after (fbyg), L1799--L1801),
then the deviation is `≲ L^{-η³} (L^{(γ+3η)/2-κη} R)²`, i.e. (excesseqn2) with the two new `α`-atoms labelled `(R, κ)`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

/-- The bound for the number of choices `𝔉` of the labels of a single vine with `m` atoms (L1799--L1801):
`L^d (ρL)^d L^{(m-2)(d-γ)} δ^{-m/2} (log L)^e ∏𝔛^{-z}` times a constant. -/
noncomputable def vineF (d : ℕ) (L γ δ ρ Cf Λ : ℝ) (m e : ℕ) : ℝ :=
  Cf * L ^ d * (ρ * L) ^ d * L ^(((m : ℝ) - 2) * ((d : ℝ) - γ)) * δ ^ (-(m : ℝ) / 2) * Real.log L ^ e / Λ

theorem encard_le_floor {α : Type*} {s : Set α} {b : ℝ} (h : s.encard ≤ ENNReal.ofReal b) :
    s.encard ≤ ((⌊b⌋₊ : ℕ) : ℕ∞) := by
  have hfin : s.encard ≠ ⊤ := fun ht => by rw [ht] at h; exact absurd h (by simp)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hn] at h ⊢
  have h2 : ((n : ℕ∞) : ℝ≥0∞) = (n : ℝ≥0∞) := by simp
  rw [h2] at h
  by_cases hb : 0 ≤ b
  · rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_le_ofReal_iff hb] at h
    exact_mod_cast Nat.le_floor h
  · have : ENNReal.ofReal b = 0 := ENNReal.ofReal_of_nonpos (by linarith)
    rw [this] at h
    have : n = 0 := by exact_mod_cast le_zero_iff.mp h
    simp [this]

end WaveTurbulence.FinalCount
