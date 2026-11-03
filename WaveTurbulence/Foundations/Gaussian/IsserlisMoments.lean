/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Gaussian.ComplexGaussian
public import Mathlib.Probability.Independence.Integration
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Factorization of signed Gaussian moments

The analytic step in the proof of DH21 Lemma A.2: group repeated indices and use
independence and the scalar complex Gaussian moment formula. Boolean `true` means
an unconjugated factor and `false` means a conjugated factor.
-/

public section

open MeasureTheory ProbabilityTheory

namespace WaveTurbulence

/-- Group a signed product according to its Gaussian index. -/
theorem prod_signed_eq_prod_monomial {J ι : Type*} [DecidableEq J] [DecidableEq ι]
    (s : Finset J) (k : J → ι) (ζ : J → Bool) (g : ι → ℂ) :
    (∏ j ∈ s, if ζ j then g (k j) else star (g (k j))) =
      ∏ i ∈ s.image k,
        g i ^ (s.filter (fun j => k j = i ∧ ζ j = true)).card *
          star (g i) ^ (s.filter (fun j => k j = i ∧ ζ j = false)).card := by
  classical
  rw [← Finset.prod_fiberwise_of_maps_to (s := s) (t := s.image k)
    (g := k) (fun j hj => Finset.mem_image_of_mem k hj)]
  apply Finset.prod_congr rfl
  intro i _
  have he : (∏ j ∈ s.filter (fun j => k j = i),
      if ζ j then g (k j) else star (g (k j))) =
      ∏ j ∈ s.filter (fun j => k j = i), if ζ j then g i else star (g i) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [(Finset.mem_filter.mp hj).2]
  rw [he, Finset.prod_ite]
  simp only [Finset.prod_const, Finset.filter_filter, Bool.not_eq_true]

/-- The independent-index product form of the signed Gaussian moment (DH21 Lemma A.2).
Indices in `k` may repeat. The pairing interpretation is a separate combinatorial step. -/
theorem integral_signed_prod_eq_prod_factorial {Ω J ι : Type*} [MeasurableSpace Ω]
    [DecidableEq J] [DecidableEq ι] {P : Measure Ω} {η : ι → Ω → ℂ}
    (hη : iIndepFun η P) (hlaw : ∀ i, HasLaw (η i) stdComplexGaussian P)
    (s : Finset J) (k : J → ι) (ζ : J → Bool) :
    (∫ ω, ∏ j ∈ s, if ζ j then η (k j) ω else star (η (k j) ω) ∂P) =
      ∏ i ∈ s.image k,
        if (s.filter (fun j => k j = i ∧ ζ j = true)).card =
            (s.filter (fun j => k j = i ∧ ζ j = false)).card
        then (((s.filter (fun j => k j = i ∧ ζ j = true)).card).factorial : ℂ)
        else 0 := by
  classical
  have he (ω : Ω) := prod_signed_eq_prod_monomial s k ζ (fun i => η i ω)
  simp_rw [he]
  have h := (hη.restrict (s.image k)).integral_fun_prod_comp
    (fun i => (hlaw i).aemeasurable)
    (f := fun i z => z ^ (s.filter (fun j => k j = i.1 ∧ ζ j = true)).card *
      star z ^ (s.filter (fun j => k j = i.1 ∧ ζ j = false)).card)
    (fun _ => by fun_prop)
  simp only [Finset.restrict_def] at h
  have hp (ω : Ω) := Finset.prod_coe_sort (s.image k)
    (fun i => η i ω ^ (s.filter (fun j => k j = i ∧ ζ j = true)).card *
      star (η i ω) ^ (s.filter (fun j => k j = i ∧ ζ j = false)).card)
  have hq := Finset.prod_coe_sort (s.image k)
    (fun i => ∫ ω, η i ω ^ (s.filter (fun j => k j = i ∧ ζ j = true)).card *
      star (η i ω) ^ (s.filter (fun j => k j = i ∧ ζ j = false)).card ∂P)
  simp_rw [hp] at h
  rw [hq] at h
  rw [h]
  apply Finset.prod_congr rfl
  intro i _
  exact integral_monomial_of_hasLaw_stdComplexGaussian (hlaw i) _ _

/-- Every finite signed product is integrable; repeated indices cause no difficulty. -/
theorem integrable_signed_prod {Ω J ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {η : ι → Ω → ℂ} (hη : iIndepFun η P)
    (hlaw : ∀ i, HasLaw (η i) stdComplexGaussian P)
    (s : Finset J) (k : J → ι) (ζ : J → Bool) :
    Integrable (fun ω => ∏ j ∈ s, if ζ j then η (k j) ω else star (η (k j) ω)) P := by
  have := hη.isProbabilityMeasure
  classical
  by_cases hs : s = ∅
  · subst s
    simp only [Finset.prod_empty]
    exact integrable_const _
  have hcard : s.card ≠ 0 := Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
  have hm (j : J) : MemLp (fun ω => if ζ j then η (k j) ω else star (η (k j) ω))
      (s.card : ENNReal) P := by
    have h := (hlaw (k j)).memLp (memLp_id_stdComplexGaussian (s.card : NNReal))
    cases hz : ζ j
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hh : MemLp (η (k j)) (s.card : ENNReal) P := by
        simpa only [ENNReal.coe_natCast] using h
      exact MemLp.ae_eq (Filter.Eventually.of_forall (fun ω => Pi.star_apply _ ω)) hh.star
    · simpa only [hz, ↓reduceIte, ENNReal.coe_natCast] using h
  have hp := MemLp.fun_prod (p := fun _ : J => (s.card : ENNReal))
    (s := s) (fun j _ => hm j)
  have hexp : (∑ _j ∈ s, (s.card : ENNReal)⁻¹)⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul,
      ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr hcard) (by simp), inv_one]
  rw [hexp] at hp
  exact memLp_one_iff_integrable.mp hp

end WaveTurbulence
