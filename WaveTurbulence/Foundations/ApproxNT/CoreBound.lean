/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.Factors

/-!
# The core estimate: major and minor arcs for products of cells (packet NT6)

This is the heart of DH21 Prop 6.1's proof (with DH23's lemmas), for the decoupled sums of
`Core.lean`. With `φ = χ₀(·/(2L))` (major arcs `|s| ≲ L`) and `ψ = 1 - φ`, and writing
`aᵢ = cellSum(μ sᵢ) = L^{2d}(Tᵢ + Nᵢ)` and `bᵢ = L^{2d} Tᵢ`,

`∏ aᵢ - ∏ bᵢ = (∏ aᵢ - ∏ φᵢaᵢ) + (∏ φᵢaᵢ - ∏ φᵢbᵢ) + (∏ φᵢbᵢ - ∏ bᵢ)`.

The first group is the minor arc (`2^n - 1` terms indexed by `∅ ≠ F`, DH23 Lemma 6.6(2) for
`i ∈ F`), the second is `I_major-C` (nonzero Poisson modes, DH23 Lemma 6.5(2), telescoped in
the index carrying a nonzero mode), the third is `I_major-B` (the tail `|s| ≳ L`). Every term is
a product of one-variable integrals, weighted by `sup |Φ̂(s)| ∏_{i∈F} ⟨sᵢ⟩^{2d}`.
-/

public section

noncomputable section

open MeasureTheory Metric WithLp Finset Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.ApproxNT

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Integration of a product function against a constant. -/
theorem lintegral_const_mul_prod_le (c : ℝ) (g : ι → ℝ → ℝ≥0∞) (hg : ∀ i, Measurable (g i))
    (B : ι → ℝ) (hB0 : ∀ i, 0 ≤ B i) (hB : ∀ i, ∫⁻ t, g i t ≤ ENNReal.ofReal (B i)) :
    ∫⁻ s : ι → ℝ, ENNReal.ofReal c * ∏ i, g i (s i) ≤ ENNReal.ofReal (c * ∏ i, B i) := by
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [show (volume : Measure (ι → ℝ)) = Measure.pi fun _ => volume from rfl,
    lintegral_fintype_prod_eq_prod g hg]
  by_cases hc : c ≤ 0
  · rw [ENNReal.ofReal_of_nonpos hc, zero_mul]; exact zero_le
  · rw [not_le] at hc
    rw [ENNReal.ofReal_mul hc.le, ENNReal.ofReal_prod_of_nonneg fun i _ => hB0 i]
    gcongr with i
    exact hB i

/-- The data of one cell for each index, at scale `L` and time scale `μ`. -/
structure CellData (d : ℕ) (ι : Type*) where
  /-- First centers. -/
  p : ι → Mom d
  /-- Second centers. -/
  q : ι → Mom d
  /-- First frequencies. -/
  ξ : ι → Mom d
  /-- Second frequencies. -/
  ζ : ι → Mom d

/-- The pointwise decomposition into minor arcs, nonzero modes and the major-arc tail. -/
theorem enorm_prod_scS_sub_prod_scT_le {L : ℝ} (hL : 0 < L) (μ : ℝ) (c : CellData d ι)
    (s : ι → ℝ) :
    ‖∏ i, scS L μ (c.p i) (c.q i) (c.ξ i) (c.ζ i) (s i) -
        ∏ i, scT L μ (c.p i) (c.q i) (c.ξ i) (c.ζ i) (s i)‖ₑ ≤
      (∑ F ∈ (univ : Finset ι).powerset.erase ∅,
        (∏ i ∈ F, ‖scMin L μ (s i) * scS L μ (c.p i) (c.q i) (c.ξ i) (c.ζ i) (s i)‖ₑ) *
          ∏ i ∈ univ \ F, ‖scMaj L μ (s i) * scS L μ (c.p i) (c.q i) (c.ξ i) (c.ζ i) (s i)‖ₑ) +
      (∑ l, ‖scMaj L μ (s l) * scN L μ (c.p l) (c.q l) (c.ξ l) (c.ζ l) (s l)‖ₑ *
        ∏ i ∈ univ.erase l,
          (‖scMaj L μ (s i) * (scT L μ (c.p i) (c.q i) (c.ξ i) (c.ζ i) (s i) +
              scN L μ (c.p i) (c.q i) (c.ξ i) (c.ζ i) (s i))‖ₑ +
            ‖scMaj L μ (s i) * scT L μ (c.p i) (c.q i) (c.ξ i) (c.ζ i) (s i)‖ₑ)) +
      (∑ l, ‖scMin L μ (s l) * scT L μ (c.p l) (c.q l) (c.ξ l) (c.ζ l) (s l)‖ₑ *
        ∏ i ∈ univ.erase l,
          (‖scMaj L μ (s i) * scT L μ (c.p i) (c.q i) (c.ξ i) (c.ζ i) (s i)‖ₑ +
            ‖scT L μ (c.p i) (c.q i) (c.ξ i) (c.ζ i) (s i)‖ₑ)) := by
  set a : ι → ℂ := fun i => scS L μ (c.p i) (c.q i) (c.ξ i) (c.ζ i) (s i)
  set b : ι → ℂ := fun i => scT L μ (c.p i) (c.q i) (c.ξ i) (c.ζ i) (s i)
  set n : ι → ℂ := fun i => scN L μ (c.p i) (c.q i) (c.ξ i) (c.ζ i) (s i)
  set φ : ι → ℂ := fun i => scMaj L μ (s i)
  set ψ : ι → ℂ := fun i => scMin L μ (s i)
  have hφψ : ∀ i, φ i + ψ i = 1 := fun i => scMaj_add_scMin L μ (s i)
  have ha : ∀ i, a i = b i + n i := fun i => scS_eq hL μ _ _ _ _ _
  have hsplit : ∏ i, a i - ∏ i, b i =
      (∏ i, (φ i * a i + ψ i * a i) - ∏ i, φ i * a i) +
        (∏ i, φ i * (b i + n i) - ∏ i, φ i * b i) + (∏ i, φ i * b i - ∏ i, b i) := by
    have h1 : ∀ i, φ i * a i + ψ i * a i = a i := fun i => by rw [← add_mul, hφψ, one_mul]
    have h2 : ∀ i, φ i * (b i + n i) = φ i * a i := fun i => by rw [ha]
    simp_rw [h1, h2]
    ring
  rw [hsplit]
  refine (enorm_add_le _ _).trans (add_le_add ((enorm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · exact enorm_prod_add_sub_prod_le (fun i => φ i * a i) (fun i => ψ i * a i)
  · refine (enorm_prod_sub_prod_le univ (fun i => φ i * (b i + n i)) (fun i => φ i * b i)).trans
      (le_of_eq ?_)
    refine sum_congr rfl fun l _ => ?_
    congr 2
    ring
  · refine (enorm_prod_sub_prod_le univ (fun i => φ i * b i) b).trans (le_of_eq ?_)
    refine sum_congr rfl fun l _ => ?_
    congr 1
    have : φ l * b l - b l = -(ψ l * b l) := by
      have := hφψ l
      linear_combination b l * this
    rw [this, enorm_neg]

end WaveTurbulence.ApproxNT
