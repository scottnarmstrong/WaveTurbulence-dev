/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cumulant.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Symmetry of moments and cumulants

TARGET `gaugeinv` (L567–L570) and Definition `defcm`: the argument works for
unnormalized restricted measures, since it uses equality of joint laws and
scalar homogeneity, rather than conditional probability.
-/

public section

open MeasureTheory

namespace WaveTurbulence

/-- A finite product moment depends only on the joint pushforward measure. -/
theorem integral_prod_congr_map {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} {X : ι → Ω → ℂ} {Y : ι → Ω' → ℂ}
    (hX : ∀ j, Measurable (X j)) (hY : ∀ j, Measurable (Y j))
    (hmap : μ.map (fun ω j => X j ω) = ν.map (fun ω j => Y j ω)) (s : Finset ι) :
    (∫ ω, ∏ j ∈ s, X j ω ∂μ) = ∫ ω, ∏ j ∈ s, Y j ω ∂ν := by
  have hF : Measurable (fun v : ι → ℂ => ∏ j ∈ s, v j) := by fun_prop
  calc
    _ = ∫ v : ι → ℂ, ∏ j ∈ s, v j ∂μ.map (fun ω j => X j ω) :=
      (integral_map (Measurable.of_eval hX).aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ v : ι → ℂ, ∏ j ∈ s, v j ∂ν.map (fun ω j => Y j ω) := by rw [hmap]
    _ = _ := integral_map (Measurable.of_eval hY).aemeasurable hF.aestronglyMeasurable

/-- Cumulants depend only on the joint pushforward measure, without normalizing it. -/
theorem cumulant_congr_map {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [DecidableEq ι] {μ : Measure Ω} {ν : Measure Ω'}
    {X : ι → Ω → ℂ} {Y : ι → Ω' → ℂ}
    (hX : ∀ j, Measurable (X j)) (hY : ∀ j, Measurable (Y j))
    (hmap : μ.map (fun ω j => X j ω) = ν.map (fun ω j => Y j ω)) (s : Finset ι) :
    cumulant μ X s = cumulant ν Y s := by
  unfold cumulant
  apply Finset.sum_congr rfl
  intro P _
  apply congrArg (fun z : ℂ => (-1 : ℂ) ^ (P.parts.card - 1) *
    ((P.parts.card - 1).factorial : ℂ) * z)
  apply Finset.prod_congr rfl
  intro A _
  exact integral_prod_congr_map hX hY hmap A

/-- An invariant joint law with a nontrivial product of scalar factors forces a moment to vanish. -/
theorem integral_prod_eq_zero_of_map_mul {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : ι → Ω → ℂ} (hX : ∀ j, Measurable (X j))
    (c : ι → ℂ) (s : Finset ι)
    (hmap : μ.map (fun ω j => X j ω) = μ.map (fun ω j => c j * X j ω))
    (hc : (∏ j ∈ s, c j) ≠ 1) : (∫ ω, ∏ j ∈ s, X j ω ∂μ) = 0 := by
  have h := integral_prod_congr_map (Y := fun j ω => c j * X j ω) hX (fun j => measurable_const.mul (hX j)) hmap s
  simp_rw [Finset.prod_mul_distrib] at h
  rw [integral_const_mul] at h
  have hz : (1 - ∏ j ∈ s, c j) * (∫ ω, ∏ j ∈ s, X j ω ∂μ) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm hc))

/-- The same joint-law symmetry forces a cumulant to vanish. -/
theorem cumulant_eq_zero_of_map_mul {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {μ : Measure Ω} {X : ι → Ω → ℂ} (hX : ∀ j, Measurable (X j))
    (c : ι → ℂ) (s : Finset ι)
    (hmap : μ.map (fun ω j => X j ω) = μ.map (fun ω j => c j * X j ω))
    (hc : (∏ j ∈ s, c j) ≠ 1) : cumulant μ X s = 0 := by
  have h := cumulant_congr_map (Y := fun j ω => c j * X j ω) hX (fun j => measurable_const.mul (hX j)) hmap s
  rw [cumulant_mul] at h
  have hz : (1 - ∏ j ∈ s, c j) * cumulant μ X s = 0 := by linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm hc))

end WaveTurbulence

namespace WaveTurbulence

/-- The product gauge factor is the exponential of the total charge. -/
theorem prod_gauge_factor {ι : Type*} (s : Finset ι) (q : ι → ℝ) (θ : ℝ) :
    (∏ j ∈ s, Complex.exp (Complex.ofReal (q j * θ) * Complex.I)) =
      Complex.exp (Complex.ofReal ((∑ j ∈ s, q j) * θ) * Complex.I) := by
  rw [← Complex.exp_sum, ← Finset.sum_mul, ← Complex.ofReal_sum, ← Finset.sum_mul]

private theorem prod_gauge_factor_ne_one {ι : Type*} (s : Finset ι) (q : ι → ℝ)
    (hq : (∑ j ∈ s, q j) ≠ 0) :
    (∏ j ∈ s, Complex.exp (Complex.ofReal (q j * (Real.pi / (∑ j ∈ s, q j))) * Complex.I)) ≠ 1 := by
  rw [prod_gauge_factor]
  have hmul : (∑ j ∈ s, q j) * (Real.pi / (∑ j ∈ s, q j)) = Real.pi := by
    field_simp
  rw [hmul, Complex.exp_pi_mul_I]
  norm_num

/-- Gauge-invariant joint laws have vanishing moments at nonzero total charge
(TARGET `gaugeinv`). This includes arbitrary finite restricted measures. -/
theorem integral_prod_eq_zero_of_gauge_invariant {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : ι → Ω → ℂ} (hX : ∀ j, Measurable (X j)) (q : ι → ℝ)
    (hinv : ∀ θ : ℝ, μ.map (fun ω j => X j ω) =
      μ.map (fun ω j => Complex.exp (Complex.ofReal (q j * θ) * Complex.I) * X j ω))
    (s : Finset ι) (hq : (∑ j ∈ s, q j) ≠ 0) :
    (∫ ω, ∏ j ∈ s, X j ω ∂μ) = 0 :=
  integral_prod_eq_zero_of_map_mul hX _ s (hinv (Real.pi / (∑ j ∈ s, q j)))
    (prod_gauge_factor_ne_one s q hq)

/-- Gauge-invariant joint laws have vanishing cumulants at nonzero total charge
(TARGET Definition `defcm`, following `gaugeinv`). -/
theorem cumulant_eq_zero_of_gauge_invariant {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {μ : Measure Ω} {X : ι → Ω → ℂ} (hX : ∀ j, Measurable (X j)) (q : ι → ℝ)
    (hinv : ∀ θ : ℝ, μ.map (fun ω j => X j ω) =
      μ.map (fun ω j => Complex.exp (Complex.ofReal (q j * θ) * Complex.I) * X j ω))
    (s : Finset ι) (hq : (∑ j ∈ s, q j) ≠ 0) : cumulant μ X s = 0 :=
  cumulant_eq_zero_of_map_mul hX _ s (hinv (Real.pi / (∑ j ∈ s, q j)))
    (prod_gauge_factor_ne_one s q hq)

end WaveTurbulence

namespace WaveTurbulence

private theorem exists_nonzero_charge_coordinate {ι : Type*} {d : ℕ}
    (s : Finset ι) (q : ι → Fin d → ℝ) (hq : (∑ j ∈ s, q j) ≠ 0) :
    ∃ l : Fin d, (∑ j ∈ s, q j l) ≠ 0 := by
  by_contra h
  push Not at h
  apply hq
  funext l
  simpa only [Finset.sum_apply, Pi.zero_apply] using h l

private theorem map_coordinate_gauge_invariant {Ω ι : Type*} [MeasurableSpace Ω] {d : ℕ}
    {μ : Measure Ω} {X : ι → Ω → ℂ} (q : ι → Fin d → ℝ)
    (hinv : ∀ x : Fin d → ℝ, μ.map (fun ω j => X j ω) =
      μ.map (fun ω j => Complex.exp (Complex.ofReal (∑ l, q j l * x l) * Complex.I) * X j ω))
    (l : Fin d) (θ : ℝ) :
    μ.map (fun ω j => X j ω) =
      μ.map (fun ω j => Complex.exp (Complex.ofReal (q j l * θ) * Complex.I) * X j ω) := by
  simpa [Pi.single_apply, mul_ite] using hinv (Pi.single l θ)

/-- Translation-invariant joint laws have vanishing moments at nonzero total momentum
(TARGET `gaugeinv`). Here `q j` denotes the signed momentum of entry `j`. -/
theorem integral_prod_eq_zero_of_translation_invariant {Ω ι : Type*} [MeasurableSpace Ω]
    {d : ℕ} {μ : Measure Ω} {X : ι → Ω → ℂ} (hX : ∀ j, Measurable (X j))
    (q : ι → Fin d → ℝ)
    (hinv : ∀ x : Fin d → ℝ, μ.map (fun ω j => X j ω) =
      μ.map (fun ω j => Complex.exp (Complex.ofReal (∑ l, q j l * x l) * Complex.I) * X j ω))
    (s : Finset ι) (hq : (∑ j ∈ s, q j) ≠ 0) :
    (∫ ω, ∏ j ∈ s, X j ω ∂μ) = 0 := by
  obtain ⟨l, hl⟩ := exists_nonzero_charge_coordinate s q hq
  exact integral_prod_eq_zero_of_gauge_invariant hX (fun j => q j l)
    (map_coordinate_gauge_invariant q hinv l) s hl

/-- Translation-invariant joint laws have vanishing cumulants at nonzero total momentum
(TARGET Definition `defcm`, following `gaugeinv`). -/
theorem cumulant_eq_zero_of_translation_invariant {Ω ι : Type*} [MeasurableSpace Ω]
    [DecidableEq ι] {d : ℕ} {μ : Measure Ω} {X : ι → Ω → ℂ} (hX : ∀ j, Measurable (X j))
    (q : ι → Fin d → ℝ)
    (hinv : ∀ x : Fin d → ℝ, μ.map (fun ω j => X j ω) =
      μ.map (fun ω j => Complex.exp (Complex.ofReal (∑ l, q j l * x l) * Complex.I) * X j ω))
    (s : Finset ι) (hq : (∑ j ∈ s, q j) ≠ 0) : cumulant μ X s = 0 := by
  obtain ⟨l, hl⟩ := exists_nonzero_charge_coordinate s q hq
  exact cumulant_eq_zero_of_gauge_invariant hX (fun j => q j l)
    (map_coordinate_gauge_invariant q hinv l) s hl

end WaveTurbulence
