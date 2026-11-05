/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Cumulant.Basic
/-! Multilinearity infrastructure for T.cmattr and the b-contributions of S6. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset

theorem cumulant_congr_on {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) {X Y : ι → Ω → ℂ} (s : Finset ι)
    (h : ∀ j ∈ s, ∀ ω, X j ω = Y j ω) : cumulant μ X s = cumulant μ Y s := by
  unfold cumulant
  apply Finset.sum_congr rfl
  intro P _
  congr 1
  apply Finset.prod_congr rfl
  intro J hJ
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => Finset.prod_congr rfl (fun j hj => h j (P.le hJ hj) ω))

theorem cumulant_update_zero {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (X : ι → Ω → ℂ) (s : Finset ι) {i : ι} (hi : i ∈ s) :
    cumulant μ (Function.update X i 0) s = 0 := by
  classical
  unfold cumulant
  apply Finset.sum_eq_zero
  intro P _
  have hz : (∫ ω, ∏ j ∈ P.part i, Function.update X i 0 j ω ∂μ) = 0 := by
    have he : (fun ω => ∏ j ∈ P.part i, Function.update X i 0 j ω) = fun _ => (0 : ℂ) := by
      funext ω
      exact Finset.prod_eq_zero (P.mem_part hi) (by simp)
    rw [he, integral_zero]
  rw [Finset.prod_eq_zero (P.part_mem.mpr hi) hz, mul_zero]

/-- Additivity in one actual cumulant argument. Integrability is required only for the
finite block moments to which Bochner additivity is applied. -/
theorem cumulant_add_update {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (X : ι → Ω → ℂ) (s : Finset ι) {i : ι} (hi : i ∈ s)
    (f g : Ω → ℂ)
    (hf : ∀ J ⊆ s, Integrable (fun ω => ∏ j ∈ J, Function.update X i f j ω) μ)
    (hg : ∀ J ⊆ s, Integrable (fun ω => ∏ j ∈ J, Function.update X i g j ω) μ) :
    cumulant μ (Function.update X i (f + g)) s =
      cumulant μ (Function.update X i f) s + cumulant μ (Function.update X i g) s := by
  classical
  unfold cumulant
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro P _
  rw [← mul_add]
  congr 1
  symm
  apply Finset.prod_add_prod_eq (P.part_mem.mpr hi)
  · have he : (fun ω => ∏ j ∈ P.part i, Function.update X i (f + g) j ω) =
        (fun ω => ∏ j ∈ P.part i, Function.update X i f j ω) +
          (fun ω => ∏ j ∈ P.part i, Function.update X i g j ω) := by
      funext ω
      symm
      apply Finset.prod_add_prod_eq (P.mem_part hi)
      · simp
      · intro j _ hji
        simp [hji]
      · intro j _ hji
        simp [hji]
    rw [he]
    exact (integral_add (hf _ (P.part_subset i)) (hg _ (P.part_subset i))).symm
  · intro J hJ hJi
    have hnot : i ∉ J := fun hij => hJi (P.part_eq_of_mem hJ hij).symm
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => Finset.prod_congr rfl (fun j hj => by
      have hji : j ≠ i := fun h => hnot (h ▸ hj)
      simp [hji]))
  · intro J hJ hJi
    have hnot : i ∉ J := fun hij => hJi (P.part_eq_of_mem hJ hij).symm
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => Finset.prod_congr rfl (fun j hj => by
      have hji : j ≠ i := fun h => hnot (h ▸ hj)
      simp [hji]))

/-- Distribute a finite sum in one product coordinate before taking expectations. -/
theorem prod_update_sum {Ω ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (X : ι → Ω → ℂ) (s : Finset ι) {i : ι} (hi : i ∈ s)
    (t : Finset α) (F : α → Ω → ℂ) (ω : Ω) :
    (∏ j ∈ s, Function.update X i (∑ a ∈ t, F a) j ω) =
      ∑ a ∈ t, ∏ j ∈ s, Function.update X i (F a) j ω := by
  induction t using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact Finset.prod_eq_zero hi (by simp)
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    rw [← ih]
    symm
    apply Finset.prod_add_prod_eq hi
    · simp
    · intro j _ hji
      simp [hji]
    · intro j _ hji
      simp [hji]

/-- Block-product integrability for the finite-sum argument. -/
theorem integrable_prod_update_sum {Ω ι α : Type*} [MeasurableSpace Ω]
    [DecidableEq ι] [DecidableEq α] (μ : Measure Ω) (X : ι → Ω → ℂ)
    (s : Finset ι) (i : ι) (t : Finset α) (F : α → Ω → ℂ)
    (hrest : ∀ J ⊆ s, i ∉ J → Integrable (fun ω => ∏ j ∈ J, X j ω) μ)
    (hF : ∀ a ∈ t, ∀ J ⊆ s, Integrable (fun ω => ∏ j ∈ J, Function.update X i (F a) j ω) μ) :
    ∀ J ⊆ s, Integrable (fun ω => ∏ j ∈ J, Function.update X i (∑ a ∈ t, F a) j ω) μ := by
  intro J hJ
  by_cases hiJ : i ∈ J
  · have he : (fun ω => ∏ j ∈ J, Function.update X i (∑ a ∈ t, F a) j ω) =
        fun ω => ∑ a ∈ t, ∏ j ∈ J, Function.update X i (F a) j ω :=
      funext (fun ω => prod_update_sum X J hiJ t F ω)
    rw [he]
    exact integrable_finsetSum t (fun a ha => hF a ha J hJ)
  · apply (hrest J hJ hiJ).congr
    apply Filter.Eventually.of_forall
    intro ω
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := fun h => hiJ (h ▸ hj)
    simp [hji]

/-- Finite-sum multilinearity in one nonempty cumulant coordinate, the analytic
finite-tree expansion step of T.cmattr. No integrability of the unused original Xi is assumed. -/
theorem cumulant_sum_update {Ω ι α : Type*} [MeasurableSpace Ω]
    [DecidableEq ι] [DecidableEq α] (μ : Measure Ω) (X : ι → Ω → ℂ)
    (s : Finset ι) {i : ι} (hi : i ∈ s) (t : Finset α) (F : α → Ω → ℂ)
    (hF : ∀ a ∈ t, ∀ J ⊆ s, Integrable (fun ω => ∏ j ∈ J, Function.update X i (F a) j ω) μ) :
    cumulant μ (Function.update X i (∑ a ∈ t, F a)) s =
      ∑ a ∈ t, cumulant μ (Function.update X i (F a)) s := by
  induction t using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact cumulant_update_zero μ X s hi
  | @insert a t ha ih =>
    have hfa := hF a (Finset.mem_insert_self _ _)
    have hft := fun b hb => hF b (Finset.mem_insert_of_mem hb)
    have hrest : ∀ J ⊆ s, i ∉ J → Integrable (fun ω => ∏ j ∈ J, X j ω) μ := by
      intro J hJ hiJ
      apply (hfa J hJ).congr
      apply Filter.Eventually.of_forall
      intro ω
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := fun h => hiJ (h ▸ hj)
      simp [hji]
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      cumulant_add_update μ X s hi (F a) _ hfa
        (integrable_prod_update_sum μ X s i t F hrest hft), ih hft]

end WaveTurbulence.Induct
