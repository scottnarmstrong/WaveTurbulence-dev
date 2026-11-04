/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Measurable averaging over all attaining endpoint coordinates

At a tie, divide equally among all matching coordinates. The count is
a finite sum of measurable equality indicators. Each weight lies in
[0,1], the weights sum to one whenever an endpoint is attained, and
weighted endpoint formulas require no measurable-choice theorem.
-/

public section

open MeasureTheory
open scoped Classical

namespace WaveTurbulence.Sumint

/-- Number of coordinates attaining the chosen endpoint, viewed as a real finite sum. -/
@[expose] noncomputable def endpointMatchCount {ι X : Type*} [Fintype ι]
    (f : ι → X → ℝ) (g : X → ℝ) (x : X) : ℝ :=
  ∑ v, if g x = f v x then 1 else 0

/-- Equal averaging weight on the coordinates attaining an endpoint. -/
@[expose] noncomputable def endpointMatchWeight {ι X : Type*} [Fintype ι]
    (f : ι → X → ℝ) (g : X → ℝ) (v : ι) (x : X) : ℝ :=
  if g x = f v x then (endpointMatchCount f g x)⁻¹ else 0

/-- An attained endpoint has at least one matching coordinate. -/
theorem one_le_endpointMatchCount {ι X : Type*} [Fintype ι]
    (f : ι → X → ℝ) (g : X → ℝ) (x : X) (hx : ∃ v, g x = f v x) :
    1 ≤ endpointMatchCount f g x := by
  obtain ⟨v,hv⟩ := hx
  unfold endpointMatchCount
  have hs := Finset.single_le_sum (s := Finset.univ) (f := fun w => if g x = f w x then (1:ℝ) else 0)
    (fun w _ => by split_ifs <;> norm_num) (Finset.mem_univ v)
  simpa only [ite_eq_left hv] using hs

/-- Every endpoint averaging weight lies in the closed unit interval. -/
theorem endpointMatchWeight_mem_Icc {ι X : Type*} [Fintype ι]
    (f : ι → X → ℝ) (g : X → ℝ) (x : X) (hx : ∃ v, g x = f v x) (v : ι) :
    endpointMatchWeight f g v x ∈ Set.Icc (0:ℝ) 1 := by
  have hc := one_le_endpointMatchCount f g x hx
  have hcp : 0 < endpointMatchCount f g x := zero_lt_one.trans_le hc
  unfold endpointMatchWeight
  split_ifs
  · refine ⟨inv_nonneg.mpr hcp.le,?_⟩
    rw [← one_div,div_le_iff₀ hcp]
    simpa using hc
  · exact ⟨le_rfl,zero_le_one⟩

/-- The averaging weights form an exact partition of one on every attained endpoint. -/
theorem sum_endpointMatchWeight {ι X : Type*} [Fintype ι]
    (f : ι → X → ℝ) (g : X → ℝ) (x : X) (hx : ∃ v, g x = f v x) :
    ∑ v, endpointMatchWeight f g v x = 1 := by
  have hc : endpointMatchCount f g x ≠ 0 := ne_of_gt (zero_lt_one.trans_le (one_le_endpointMatchCount f g x hx))
  have he (v : ι) : endpointMatchWeight f g v x =
      (if g x = f v x then (1:ℝ) else 0)*(endpointMatchCount f g x)⁻¹ := by
    unfold endpointMatchWeight
    split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ hc

/-- The finite match count is measurable for measurable coordinate and endpoint functions. -/
theorem measurable_endpointMatchCount {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (f : ι → X → ℝ) (g : X → ℝ) (hf : ∀ v, Measurable (f v)) (hg : Measurable g) :
    Measurable (endpointMatchCount f g) := by
  exact Finset.measurable_sum _ (fun v _ =>
    Measurable.ite (measurableSet_eq_fun hg (hf v)) measurable_const measurable_const)

/-- Every tie-averaging weight is measurable. -/
theorem measurable_endpointMatchWeight {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (f : ι → X → ℝ) (g : X → ℝ) (hf : ∀ v, Measurable (f v)) (hg : Measurable g) (v : ι) :
    Measurable (endpointMatchWeight f g v) :=
  Measurable.ite (measurableSet_eq_fun hg (hf v)) (measurable_endpointMatchCount f g hf hg).inv measurable_const

/-- Any complex endpoint formula splits exactly over the attaining coordinates. -/
theorem endpoint_formula_eq_weighted_sum {ι X : Type*} [Fintype ι]
    (f : ι → X → ℝ) (g : X → ℝ) (x : X) (hx : ∃ v, g x = f v x) (H : ℝ → ℂ) :
    H (g x) = ∑ v, (endpointMatchWeight f g v x:ℂ)*H (f v x) := by
  symm
  have he (v : ι) : (endpointMatchWeight f g v x:ℂ)*H (f v x) =
      (endpointMatchWeight f g v x:ℂ)*H (g x) := by
    by_cases hv : g x = f v x
    · rw [hv]
    · simp only [endpointMatchWeight,ite_eq_right hv,Complex.ofReal_zero,zero_mul]
  simp_rw [he]
  rw [← Finset.sum_mul,← Complex.ofReal_sum,sum_endpointMatchWeight f g x hx,Complex.ofReal_one,one_mul]

end WaveTurbulence.Sumint
