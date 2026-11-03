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

set_option backward.isDefEq.respectTransparency false in
/-- Tonelli's theorem for product functions of `n` variables. -/
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      calc
        _ = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ x, f 0 x ∂μ 0)
            * ∏ i : Fin n, ∫⁻ (x : E (Fin.succ i)), f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← n_ih (fun i => f i.succ) (fun i => hf i.succ), ← lintegral_prod_mul]
          · exact (hf 0).aemeasurable
          · exact (Finset.measurable_prod _ fun i _ =>
              (hf i.succ).comp (measurable_pi_apply i)).aemeasurable
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

/-- Tonelli's theorem for product functions, variables indexed by a finite type. -/
theorem lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    (f : (i : ι) → E i → ℝ≥0∞) {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
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

end WaveTurbulence.ApproxNT
