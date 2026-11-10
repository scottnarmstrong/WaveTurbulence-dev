/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RawModulation
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.MeasurableDensity
public import WaveTurbulence.Foundations.Cut2A.Chirp
public import WaveTurbulence.Foundations.Incoh.MomentumModulation
public import WaveTurbulence.Foundations.Incoh.SpatialCenterDecay

/-! Ported by source from C2-B-TOP `C2BTop.RootMeasure` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Root-modulated internal Fourier presentations (C2-B-TOP)

A top-node weight `g (k + ℓ_a(x))` reads the external root momentum `k` as well as the internal
paired momenta `x`.  After Fourier presentation of `g`, the root dependence is the character
`e(⟨Ξ, k⟩)` with a parameter-dependent frequency `Ξ`, multiplying an internal C2-A Fourier measure.

* `RootMeasure d n α`: a C2-A `SpatialMeasure` on the paired momenta (measurable density) together
  with a measurable root frequency `root : α → Mom d`.
* `RootMeasure.at G k`: the internal Fourier measure seen at root momentum `k`, amplitude
  `amp a * e(⟨root a, k⟩)`.  Its value is the weight at `(k, x)`.
* `RootMeasure.momentMass J G = ∫ (1 + ‖root‖)^J |amp|`: the cost of `J` root derivatives.
* `norm_iteratedFDeriv_rootChar_mul_le`: the Leibniz bound for `e(⟨Ξ, ·⟩) * A`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff
namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh WaveTurbulence.Cut2A

/-- The root character `e(⟨Ξ, k⟩)`. -/
def rootChar {d : ℕ} (Ξ k : Mom d) : ℂ := (Real.fourierChar (inner ℝ Ξ k) : ℂ)

theorem norm_rootChar {d : ℕ} (Ξ k : Mom d) : ‖rootChar Ξ k‖ = 1 := Circle.norm_coe _

theorem measurable_rootChar {d : ℕ} {α : Type*} [MeasurableSpace α] {Ξ : α → Mom d}
    (hΞ : Measurable Ξ) (k : Mom d) : Measurable (fun a => rootChar (Ξ a) k) := by
  have hc : Continuous (fun x : Mom d => rootChar x k) := by
    unfold rootChar
    exact Cut2A.character_smooth.continuous.comp (continuous_id.inner continuous_const)
  exact hc.measurable.comp hΞ

/-- A root-modulated internal Fourier presentation. -/
structure RootMeasure (d n : ℕ) (α : Type*) [MeasurableSpace α] where
  base : SpatialMeasure (PairedMomentum d n) α
  amplitude_measurable : Measurable base.amplitude
  root : α → Mom d
  root_measurable : Measurable root

namespace RootMeasure

variable {d n : ℕ} {α : Type*} [MeasurableSpace α]

/-- The internal Fourier measure seen at the external root momentum `k`. -/
def «at» (G : RootMeasure d n α) (k : Mom d) : SpatialMeasure (PairedMomentum d n) α where
  μ := G.base.μ
  sigmaFinite := G.base.sigmaFinite
  frequency := G.base.frequency
  frequency_measurable := G.base.frequency_measurable
  amplitude := fun a => G.base.amplitude a * rootChar (G.root a) k
  amplitude_integrable := by
    refine G.base.amplitude_integrable.norm.mono'
      (G.amplitude_measurable.mul (measurable_rootChar G.root_measurable k)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => ?_)
    rw [norm_mul, norm_rootChar, mul_one]

theorem at_amplitude (G : RootMeasure d n α) (k : Mom d) (a : α) :
    (G.at k).amplitude a = G.base.amplitude a * rootChar (G.root a) k := rfl

theorem at_mass (G : RootMeasure d n α) (k : Mom d) : (G.at k).mass = G.base.mass := by
  unfold SpatialMeasure.mass
  congr 1
  funext a
  rw [at_amplitude, norm_mul, norm_rootChar, mul_one]

/-- The literal value: `∫ amp a * e(⟨root a, k⟩) * e(⟨freq a, x⟩)`. -/
theorem at_value (G : RootMeasure d n α) (k : Mom d) (x : PairedMomentum d n) :
    (G.at k).value x = ∫ a, G.base.amplitude a * rootChar (G.root a) k *
      (Real.fourierChar (inner ℝ (G.base.frequency a) x) : ℂ) ∂G.base.μ := rfl

/-- The cost of `J` root derivatives. -/
def momentMass (J : ℕ) (G : RootMeasure d n α) : ℝ≥0∞ :=
  ∫⁻ a, ENNReal.ofReal ((1 + ‖G.root a‖) ^ J) * ‖G.base.amplitude a‖ₑ ∂G.base.μ

theorem measurable_momentDensity (J : ℕ) (G : RootMeasure d n α) :
    Measurable (fun a => (1 + ‖G.root a‖) ^ J * ‖G.base.amplitude a‖) :=
  ((measurable_const.add G.root_measurable.norm).pow_const J).mul G.amplitude_measurable.norm

theorem momentMass_eq (J : ℕ) (G : RootMeasure d n α) :
    G.momentMass J = ∫⁻ a, ENNReal.ofReal ((1 + ‖G.root a‖) ^ J * ‖G.base.amplitude a‖) ∂G.base.μ := by
  unfold momentMass
  congr 1
  funext a
  rw [ENNReal.ofReal_mul (by positivity), ofReal_norm]

/-- Finite moment mass gives an integrable moment density. -/
theorem integrable_momentDensity (J : ℕ) (G : RootMeasure d n α) (h : G.momentMass J < ⊤) :
    Integrable (fun a => (1 + ‖G.root a‖) ^ J * ‖G.base.amplitude a‖) G.base.μ := by
  refine ⟨(measurable_momentDensity J G).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun a => by positivity)]
  rw [← momentMass_eq]
  exact h

end RootMeasure

/-- The dimension-free Leibniz constant `2^N (2π)^N` of `N` root derivatives of a root character. -/
def rootJetConstant (N : ℕ) : ℝ := (2 : ℝ) ^ N * (2 * Real.pi) ^ N

theorem rootJetConstant_pos (N : ℕ) : 0 < rootJetConstant N := by
  unfold rootJetConstant; positivity

/-- Leibniz: `J` root derivatives of `e(⟨Ξ, ·⟩) A` cost `2^J (2π)^J (1 + ‖Ξ‖)^J` times a common
weighted envelope of the derivatives of `A`. -/
theorem norm_iteratedFDeriv_rootChar_mul_le {d N W j : ℕ} (Ξ : Mom d) {A : Mom d → ℂ}
    (hA : ContDiff ℝ N A) {v : ℝ} (hj : j ≤ N)
    (hb : ∀ i ≤ N, ∀ k, Fourier.momentumBracket k ^ W * ‖iteratedFDeriv ℝ i A k‖ ≤ v) (k : Mom d) :
    Fourier.momentumBracket k ^ W *
        ‖iteratedFDeriv ℝ j (fun k => rootChar Ξ k * A k) k‖ ≤
      rootJetConstant N * (1 + ‖Ξ‖) ^ N * v := by
  have hv : 0 ≤ v := (mul_nonneg (pow_nonneg (zero_le_one.trans (one_le_momentumBracket k)) _)
    (norm_nonneg _)).trans (hb 0 (Nat.zero_le _) k)
  have hW : 0 ≤ Fourier.momentumBracket k ^ W :=
    pow_nonneg (zero_le_one.trans (one_le_momentumBracket k)) _
  have he : ContDiff ℝ N (fun k => rootChar Ξ k) :=
    (contDiff_momentumModulation Ξ).of_le (by exact_mod_cast le_top)
  have hp := norm_iteratedFDeriv_mul_le he hA k (n := j) (by exact_mod_cast hj)
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hX : (0 : ℝ) ≤ (2 * Real.pi) ^ N * (1 + ‖Ξ‖) ^ N := by positivity
  calc
    _ ≤ Fourier.momentumBracket k ^ W * ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun k => rootChar Ξ k) k‖ *
          ‖iteratedFDeriv ℝ (j - i) A k‖ := mul_le_mul_of_nonneg_left hp hW
    _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun k => rootChar Ξ k) k‖ *
          (Fourier.momentumBracket k ^ W * ‖iteratedFDeriv ℝ (j - i) A k‖) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ((2 * Real.pi) ^ N * (1 + ‖Ξ‖) ^ N) * v := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' : i ≤ N := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hj
      have hd : ‖iteratedFDeriv ℝ i (fun k => rootChar Ξ k) k‖ ≤
          (2 * Real.pi) ^ N * (1 + ‖Ξ‖) ^ N := by
        refine (norm_iteratedFDeriv_momentumModulation_le Ξ k i).trans ?_
        exact mul_le_mul (pow_le_pow_right₀ hpi hi')
          ((pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_nonneg Ξ]) i).trans
            (pow_le_pow_right₀ (by linarith [norm_nonneg Ξ]) hi'))
          (by positivity) (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _))
        (hb (j - i) ((Nat.sub_le j i).trans hj) k) (mul_nonneg (by positivity) (norm_nonneg _))
        (mul_nonneg (Nat.cast_nonneg _) hX)
    _ = (2 : ℝ) ^ j * ((2 * Real.pi) ^ N * (1 + ‖Ξ‖) ^ N) * v := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hchoose : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
        exact_mod_cast Nat.sum_range_choose j
      rw [hchoose]
    _ ≤ (2 : ℝ) ^ N * ((2 * Real.pi) ^ N * (1 + ‖Ξ‖) ^ N) * v :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) hj) hX) hv
    _ = _ := by unfold rootJetConstant; ring

end WaveTurbulence.Flower.IncTop