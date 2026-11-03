/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Products: Tonelli for product functions and a telescoping inequality (packet NT6)

* `lintegral_fintype_prod_eq_prod`: `∫⁻ ∏ᵢ fᵢ(xᵢ) = ∏ᵢ ∫⁻ fᵢ` for measurable `fᵢ`
  (the lower-integral form of Mathlib's `integral_fintype_prod_eq_prod`);
* `norm_prod_sub_prod_le`: `|∏ aᵢ - ∏ bᵢ| ≤ ∑_ℓ |a_ℓ - b_ℓ| ∏_{i ≠ ℓ} (|aᵢ| + |bᵢ|)`.
-/

public section

noncomputable section

open MeasureTheory Finset
open scoped ENNReal

namespace WaveTurbulence.ApproxNT

/-- Tonelli's theorem for product functions of `n` variables (constant fibre). -/
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Type*} [MeasurableSpace E] {μ : Measure E}
    [SigmaFinite μ] (f : Fin n → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ x, f i x ∂μ := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
      calc
        _ = ∫⁻ x : E × (Fin n → E), f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂(μ.prod (Measure.pi (fun _ : Fin n => μ))) := by
          rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
          refine lintegral_congr fun x => ?_
          rw [Fin.prod_univ_succ]
          rfl
        _ = (∫⁻ x, f 0 x ∂μ) * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂μ := by
          rw [← n_ih (fun i => f i.succ) (fun i => hf i.succ), ← lintegral_prod_mul]
          · exact (hf 0).aemeasurable
          · exact (Finset.measurable_prod _ fun i _ =>
              (hf i.succ).comp (measurable_pi_apply i)).aemeasurable
        _ = ∏ i, ∫⁻ x, f i x ∂μ := by rw [Fin.prod_univ_succ]

/-- Tonelli's theorem for product functions, variables indexed by a finite type. -/
theorem lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι] {E : Type*} [MeasurableSpace E]
    {μ : Measure E} [SigmaFinite μ] (f : ι → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ι → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ x, f i x ∂μ := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft (fun _ : ι => μ) e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod_eq_prod (fun i => f (e i)) (fun i => hf (e i))

/-- A telescoping bound for the difference of two products. -/
theorem norm_prod_sub_prod_le {ι R : Type*} [DecidableEq ι] [NormedCommRing R]
    [NormOneClass R] (s : Finset ι) (a b : ι → R) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤
      ∑ l ∈ s, ‖a l - b l‖ * ∏ i ∈ s.erase l, (‖a i‖ + ‖b i‖) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
      rw [prod_insert hj, prod_insert hj, sum_insert hj, erase_insert hj]
      have hsplit : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i =
          (a j - b j) * ∏ i ∈ s, a i + b j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) := by ring
      rw [hsplit]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        refine (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_)
        exact le_add_of_nonneg_right (norm_nonneg _)
      · refine (norm_mul_le _ _).trans ?_
        have hl : ∀ l ∈ s, (insert j s).erase l = insert j (s.erase l) := by
          intro l hls
          exact erase_insert_of_ne (by rintro rfl; exact hj hls)
        rw [sum_congr rfl fun l hls => by
          rw [hl l hls, prod_insert (fun h => hj (mem_of_mem_erase h))]]
        calc ‖b j‖ * ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖
            ≤ ‖b j‖ * ∑ l ∈ s, ‖a l - b l‖ * ∏ i ∈ s.erase l, (‖a i‖ + ‖b i‖) :=
              mul_le_mul_of_nonneg_left ih (norm_nonneg _)
          _ ≤ (‖a j‖ + ‖b j‖) * ∑ l ∈ s, ‖a l - b l‖ * ∏ i ∈ s.erase l, (‖a i‖ + ‖b i‖) :=
              mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (norm_nonneg _))
                (sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _)
                  (prod_nonneg fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)))
          _ = ∑ l ∈ s, ‖a l - b l‖ * ((‖a j‖ + ‖b j‖) * ∏ i ∈ s.erase l, (‖a i‖ + ‖b i‖)) := by
              rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring

theorem enorm_finset_prod {ι : Type*} (s : Finset ι) (b : ι → ℂ) :
    ‖∏ i ∈ s, b i‖ₑ = ∏ i ∈ s, ‖b i‖ₑ := by
  simp only [enorm, nnnorm_prod, ENNReal.ofNNReal_finsetProd]

/-- The telescoping bound in extended nonnegative reals. -/
theorem enorm_prod_sub_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℂ) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ₑ ≤
      ∑ l ∈ s, ‖a l - b l‖ₑ * ∏ i ∈ s.erase l, (‖a i‖ₑ + ‖b i‖ₑ) := by
  have h := norm_prod_sub_prod_le s a b
  rw [← ofReal_norm]
  calc ENNReal.ofReal ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖
      ≤ ENNReal.ofReal (∑ l ∈ s, ‖a l - b l‖ * ∏ i ∈ s.erase l, (‖a i‖ + ‖b i‖)) :=
        ENNReal.ofReal_le_ofReal h
    _ = _ := by
        rw [ENNReal.ofReal_sum_of_nonneg fun l _ => mul_nonneg (norm_nonneg _)
          (prod_nonneg fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _))]
        refine sum_congr rfl fun l _ => ?_
        rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
          ENNReal.ofReal_prod_of_nonneg fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)]
        congr 1
        refine prod_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ofReal_norm, ofReal_norm]

/-- Expansion of a product of sums, minus its leading term. -/
theorem enorm_prod_add_sub_prod_le {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℂ) :
    ‖∏ i, (a i + b i) - ∏ i, a i‖ₑ ≤
      ∑ F ∈ (univ : Finset ι).powerset.erase ∅, (∏ i ∈ F, ‖b i‖ₑ) * ∏ i ∈ univ \ F, ‖a i‖ₑ := by
  have hexp : ∏ i, (a i + b i) = ∑ F ∈ (univ : Finset ι).powerset,
      (∏ i ∈ F, b i) * ∏ i ∈ univ \ F, a i := by
    rw [← prod_add (f := b) (g := a)]
    exact prod_congr rfl fun i _ => add_comm _ _
  have h0 : (∏ i ∈ (∅ : Finset ι), b i) * ∏ i ∈ univ \ ∅, a i = ∏ i, a i := by simp
  rw [hexp, ← sum_erase_add _ _ (empty_mem_powerset _), h0, add_sub_cancel_right]
  refine (enorm_sum_le _ _).trans (sum_le_sum fun F _ => ?_)
  rw [enorm_mul, enorm_finset_prod, enorm_finset_prod]

/-- A product of sums, expanded. -/
theorem prod_enorm_add_le {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℂ) :
    ∏ i, ‖a i + b i‖ₑ ≤
      ∑ F ∈ (univ : Finset ι).powerset, (∏ i ∈ F, ‖b i‖ₑ) * ∏ i ∈ univ \ F, ‖a i‖ₑ := by
  calc ∏ i, ‖a i + b i‖ₑ ≤ ∏ i, (‖b i‖ₑ + ‖a i‖ₑ) :=
        Finset.prod_le_prod fun i _ => (enorm_add_le _ _).trans (le_of_eq (add_comm _ _))
    _ = _ := prod_add _ _ _

end WaveTurbulence.ApproxNT
