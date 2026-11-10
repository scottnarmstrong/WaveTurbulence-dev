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

end WaveTurbulence.Induct
