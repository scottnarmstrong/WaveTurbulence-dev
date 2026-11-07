/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib
/-! FLOWER-P7: regrouping a double finite sum with a joint condition that depends only on finitely many data. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open Finset

theorem sum_pairs_regroup {α β D E : Type*} [DecidableEq D] [DecidableEq E] (s : Finset α) (t : Finset β)
    (dA : α → D) (dB : β → E) (J : D → E → Prop) [∀ d e, Decidable (J d e)] (f : α → ℂ) (g : β → ℂ) :
    ∑ x ∈ (s ×ˢ t).filter (fun x => J (dA x.1) (dB x.2)), f x.1 * g x.2 =
      ∑ d ∈ s.image dA, ∑ e ∈ t.image dB,
        if J d e then (∑ a ∈ s.filter (fun a => dA a = d), f a) * (∑ b ∈ t.filter (fun b => dB b = e), g b)
        else 0 := by
  classical
  rw [Finset.sum_filter, Finset.sum_product]
  have h1 : ∀ F : α → ℂ, ∑ a ∈ s, F a = ∑ d ∈ s.image dA, ∑ a ∈ s.filter (fun a => dA a = d), F a := fun F =>
    (Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image dA) (g := dA)
      (fun a ha => Finset.mem_image_of_mem _ ha) F).symm
  have h2 : ∀ F : β → ℂ, ∑ b ∈ t, F b = ∑ e ∈ t.image dB, ∑ b ∈ t.filter (fun b => dB b = e), F b := fun F =>
    (Finset.sum_fiberwise_of_maps_to (s := t) (t := t.image dB) (g := dB)
      (fun b hb => Finset.mem_image_of_mem _ hb) F).symm
  rw [h1]
  refine Finset.sum_congr rfl fun d _ => ?_
  have h3 : ∀ a ∈ s.filter (fun a => dA a = d), ∑ b ∈ t, (if J (dA a) (dB b) then f a * g b else 0) =
      ∑ e ∈ t.image dB, ∑ b ∈ t.filter (fun b => dB b = e), (if J d e then f a * g b else 0) := by
    intro a ha
    rw [h2]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun b hb => ?_
    rw [(Finset.mem_filter.1 ha).2, (Finset.mem_filter.1 hb).2]
  rw [Finset.sum_congr rfl h3, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hJ : J d e
  · simp only [hJ, if_true]
    rw [Finset.sum_mul_sum]
  · simp [hJ]

/-- Norm bound for the regrouped double sum from bounds on the slice sums (only for the data allowed by the
joint condition). -/
theorem norm_pairs_le {α β D E : Type*} [DecidableEq D] [DecidableEq E] (s : Finset α) (t : Finset β)
    (dA : α → D) (dB : β → E) (J : D → E → Prop) [∀ d e, Decidable (J d e)] (f : α → ℂ) (g : β → ℂ)
    (RA : D → Prop) (RB : E → Prop) (hJ : ∀ d e, J d e → RA d ∧ RB e)
    (bA : D → ℝ) (bB : E → ℝ)
    (hA : ∀ d ∈ s.image dA, RA d → ‖∑ a ∈ s.filter (fun a => dA a = d), f a‖ ≤ bA d)
    (hB : ∀ e ∈ t.image dB, RB e → ‖∑ b ∈ t.filter (fun b => dB b = e), g b‖ ≤ bB e) :
    ‖∑ x ∈ (s ×ˢ t).filter (fun x => J (dA x.1) (dB x.2)), f x.1 * g x.2‖ ≤
      ∑ d ∈ s.image dA, ∑ e ∈ t.image dB, if J d e then bA d * bB e else 0 := by
  rw [sum_pairs_regroup]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun e he => ?_)
  by_cases hJd : J d e
  · simp only [hJd, if_true, norm_mul]
    have hA' := hA d hd (hJ d e hJd).1
    exact mul_le_mul hA' (hB e he (hJ d e hJd).2) (norm_nonneg _) ((norm_nonneg _).trans hA')
  · simp [hJd]

end WaveTurbulence.FlowerP7
