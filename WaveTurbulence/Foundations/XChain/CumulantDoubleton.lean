/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Cumulant.Inversion
/-! The literal unnormalized two-point cumulant is covariance, including the exact mean correction. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory CumulantPartitions

private theorem selectedBlock_avoiding_pair_eq {ι : Type*} [DecidableEq ι] (i j : ι) (hne : i ≠ j)
    (B : SelectedBlock ({i, j} : Finset ι) (fun B => i ∉ B)) : B.1.1 = {j} := by
  have hsub := mem_powerset.mp B.1.2
  have hb : ∀ k ∈ B.1.1, k = j := by
    intro k hk
    rcases mem_insert.mp (hsub hk) with he | he
    · exact False.elim (B.2.2 (he ▸ hk))
    · exact mem_singleton.mp he
  obtain ⟨k, hk⟩ := B.2.1
  have hj : j ∈ B.1.1 := (hb k hk) ▸ hk
  exact subset_antisymm (fun k hk => mem_singleton.mpr (hb k hk)) (singleton_subset_iff.mpr hj)

theorem cumulant_doubleton {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (X : ι → Ω → ℂ) (i j : ι) (hne : i ≠ j) :
    cumulant μ X {i, j} = (∫ ω, X i ω * X j ω ∂μ) - (∫ ω, X i ω ∂μ) * ∫ ω, X j ω ∂μ := by
  classical
  let B0 : SelectedBlock ({i, j} : Finset ι) (fun B => i ∉ B) :=
    ⟨⟨{j}, mem_powerset.mpr (by simp)⟩, singleton_nonempty j, by simp [hne]⟩
  letI : Unique (SelectedBlock ({i, j} : Finset ι) (fun B => i ∉ B)) :=
    ⟨⟨B0⟩, fun B => Subtype.ext (Subtype.ext (selectedBlock_avoiding_pair_eq i j hne B))⟩
  have hr := partitionLog_recurrence (fun A : Finset ι => ∫ ω, ∏ k ∈ A, X k ω ∂μ)
    {i, j} i (by simp)
  change cumulant μ X {i, j} +
    (∑ B : SelectedBlock ({i, j} : Finset ι) (fun B => i ∉ B),
      cumulant μ X ({i, j} \ B.1.1) * (∫ ω, ∏ k ∈ B.1.1, X k ω ∂μ)) = _ at hr
  rw [Fintype.sum_unique] at hr
  change cumulant μ X {i, j} + cumulant μ X ({i, j} \ {j}) * (∫ ω, ∏ k ∈ ({j} : Finset ι), X k ω ∂μ) =
    (∫ ω, ∏ k ∈ ({i, j} : Finset ι), X k ω ∂μ) at hr
  have hd : ({i, j} : Finset ι) \ {j} = {i} := by
    ext k
    by_cases hi : k = i
    · subst k
      simp [hne]
    · by_cases hj : k = j
      · subst k
        simp [hne.symm]
      · simp [hi, hj]
  simp only [hd, cumulant_singleton, prod_singleton, prod_pair hne] at hr
  exact eq_sub_iff_add_eq.mpr hr

theorem cumulant_fin_two {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Fin 2 → Ω → ℂ) :
    cumulant μ X univ = (∫ ω, X 0 ω * X 1 ω ∂μ) - (∫ ω, X 0 ω ∂μ) * ∫ ω, X 1 ω ∂μ := by
  have hu : (univ : Finset (Fin 2)) = {0, 1} := by ext i; fin_cases i <;> simp
  rw [hu]
  exact cumulant_doubleton μ X 0 1 (by decide)

end WaveTurbulence.Induct
