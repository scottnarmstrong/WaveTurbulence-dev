/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.CellEnvelope
public import WaveTurbulence.Foundations.SumintPar.SummedFourierBounds
public import WaveTurbulence.Foundations.SumintPar.SourceCoefficient

/-!
# Summing primary localization coefficient masses

Finite coordinate projections reduce every partial sum over label vectors
to a finite rectangular sum. This gives the product bound without any
summability premise; the source spatial weight then makes it finite.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Finset
open scoped ENNReal FourierTransform

namespace WaveTurbulence.SumintPar

/-- The nonnegative sum of coordinate products is bounded by the product of
coordinate sums, without assuming finite support. -/
theorem tsum_product_le_product_tsum {ι : Type*} [Fintype ι] {α : ι → Type*}
    (f : ∀ i, α i → ℝ≥0∞) :
    (∑' a : ∀ i, α i, ∏ i, f i (a i)) ≤ ∏ i, ∑' x, f i x := by
  classical
  apply ENNReal.summable.tsum_le_of_sum_le
  intro S
  let choices := fun i => S.image (fun a => a i)
  have hsub : S ⊆ Fintype.piFinset choices := by
    intro a ha
    exact Fintype.mem_piFinset.mpr (fun i => mem_image.mpr ⟨a,ha,rfl⟩)
  calc
    _ ≤ ∑ a ∈ Fintype.piFinset choices, ∏ i, f i (a i) :=
      Finset.sum_le_sum_of_subset hsub
    _ = ∏ i, ∑ x ∈ choices i, f i x := (Finset.prod_univ_sum choices f).symm
    _ ≤ _ := by
      apply Finset.prod_le_prod
      intro i _
      exact ENNReal.summable.sum_le_tsum (choices i) (fun _ _ => bot_le)

/-- The primary coefficient masses are summable before any affine composition,
with only an exponential-in-M constant and their original multiplicity decay. -/
theorem tsum_primary_fourier_mass_le {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η Dsteps) (r : Mom d) :
    (∑' a : D.S.VIdx → Fin d → ℤ,
      ∏ v, ENNReal.ofReal (∫ ξ : Mom d, ‖𝓕 (localizedWeight (a v) (D.wK v r)) ξ‖)) ≤
      ENNReal.ofReal (summedCellFourierFactor d (d+1)^D.S.M *
        ∏ v, L^(-(gammaWeight d γ-Real.sqrt η)*(D.g v : ℝ))) := by
  let B := fun v : D.S.VIdx => L^(-(gammaWeight d γ-Real.sqrt η)*(D.g v : ℝ))
  have hB (v : D.S.VIdx) : 0 ≤ B v := Real.rpow_nonneg hL.le _
  have hsingle (v : D.S.VIdx) :
      (∑' a : Fin d → ℤ, ENNReal.ofReal (∫ ξ : Mom d, ‖𝓕 (localizedWeight a (D.wK v r)) ξ‖)) ≤
        ENNReal.ofReal (summedCellFourierFactor d (d+1)*B v) :=
    tsum_localizedWeight_fourier_mass_le_base hD.wN_ne_zero hD.reg.1 hD.reg.2
      (hB v) ((hD.2.2.2.2.1 v).1 r)
  calc
    _ ≤ ∏ v, ∑' a : Fin d → ℤ,
        ENNReal.ofReal (∫ ξ : Mom d, ‖𝓕 (localizedWeight a (D.wK v r)) ξ‖) :=
      tsum_product_le_product_tsum _
    _ ≤ ∏ v, ENNReal.ofReal (summedCellFourierFactor d (d+1)*B v) :=
      Finset.prod_le_prod (fun v _ => hsingle v)
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg
        (fun v _ => mul_nonneg (summedCellFourierFactor_nonneg _ _) (hB v))]
      congr 1
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,card_vector_index]

end WaveTurbulence.SumintPar
