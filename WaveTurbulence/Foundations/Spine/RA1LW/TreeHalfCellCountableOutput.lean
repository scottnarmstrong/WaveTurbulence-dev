/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.TreeHalfCellCountableFactors

/-! # Absolute output-series convergence of the original countable half-cell mixture -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT

/-- A bounded measurable factor preserves the actual summable absolute coefficient mass. -/
theorem tree_countable_bounded_coefficient_factor {I V : Type*} [MeasurableSpace V]
    (ν : Measure V) (h : I → V → ℂ) (hi : ∀ i, Integrable (h i) ν)
    (hs : Summable (fun i => ∫ v, ‖h i v‖ ∂ν)) (F : I → V → ℂ)
    (hmF : ∀ i, StronglyMeasurable (F i)) {M : ℝ} (hbF : ∀ i v, ‖F i v‖ ≤ M) :
    (∀ i, Integrable (fun v => h i v*F i v) ν) ∧
      Summable (fun i => ∫ v, h i v*F i v ∂ν) := by
  have hiF (i) : Integrable (fun v => h i v*F i v) ν :=
    (hi i).mul_bdd (hmF i).aestronglyMeasurable (ae_of_all _ (hbF i))
  refine ⟨hiF,?_⟩
  apply Summable.of_norm_bounded (hs.mul_left M)
  intro i
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  apply integral_mono (hiF i).norm ((hi i).norm.const_mul M)
  intro v
  dsimp only
  rw [norm_mul,mul_comm M]
  exact mul_le_mul_of_nonneg_left (hbF i v) (norm_nonneg _)

variable {I U : Type*} [MeasurableSpace U] {d n : ℕ}

/-- Actual physical-cell output factors preserve joint integrability and countable summability. -/
theorem tree_halfCell_countableFn_integrable_summable (μ : Measure U) [SFinite μ] (hn : 0 < n)
    (z : I → (Fin n × Fin 2) → Fin d → ℤ)
    (β γ : U → Fin n → Mom d) (hβ : Measurable β) (hγ : Measurable γ)
    (a : I → U → ℂ) (ha : ∀ c, StronglyMeasurable (a c))
    (hi : ∀ c, Integrable (fun u => ‖a c u‖*(1+((∑ j, ‖β u j‖)+(∑ j, ‖γ u j‖)))) μ)
    (hs : Summable (fun c => ∫ u, ‖a c u‖*(1+((∑ j, ‖β u j‖)+(∑ j, ‖γ u j‖))) ∂μ))
    (x y : Fin n → Mom d) :
    (∀ i : TreeHalfCellOrdinaryIndex z,
      Integrable (fun p : U × ((Fin n → Mom d) × (Fin n → Mom d)) =>
        treeHalfCellCountableCoefficient z β γ a i p*treeHalfCellOrdinaryFn z i p.2 x y) (μ.prod volume)) ∧
      Summable (fun i : TreeHalfCellOrdinaryIndex z =>
        ∫ p : U × ((Fin n → Mom d) × (Fin n → Mom d)),
          treeHalfCellCountableCoefficient z β γ a i p*treeHalfCellOrdinaryFn z i p.2 x y ∂μ.prod volume) := by
  have := isFiniteMeasureOnCompacts_pairs (n := n) (d := d)
  exact tree_countable_bounded_coefficient_factor (μ.prod volume)
    (treeHalfCellCountableCoefficient z β γ a)
    (integrable_treeHalfCellCountableCoefficient μ hn z β γ hβ hγ a ha hi)
    (summable_integral_norm_treeHalfCellCountableCoefficient μ hn z β γ hβ hγ a ha hi hs)
    (fun i p => treeHalfCellOrdinaryFn z i p.2 x y)
    (fun i => (stronglyMeasurable_treeHalfCellOrdinaryFn z i x y).comp_measurable measurable_snd)
    (fun i p => norm_treeHalfCellOrdinaryFn_le_one z i p.2 x y)

/-- Actual singular output factors preserve joint integrability and countable summability. -/
theorem tree_halfCell_countableOp_integrable_summable (μ : Measure U) [SFinite μ]
    (hd : 3 ≤ d) (hn : 0 < n) (J : Finset (Fin n))
    (z : I → (Fin n × Fin 2) → Fin d → ℤ)
    (β γ : U → Fin n → Mom d) (hβ : Measurable β) (hγ : Measurable γ)
    (a : I → U → ℂ) (ha : ∀ c, StronglyMeasurable (a c))
    (hi : ∀ c, Integrable (fun u => ‖a c u‖*(1+((∑ j, ‖β u j‖)+(∑ j, ‖γ u j‖)))) μ)
    (hs : Summable (fun c => ∫ u, ‖a c u‖*(1+((∑ j, ‖β u j‖)+(∑ j, ‖γ u j‖))) ∂μ)) :
    (∀ i : TreeHalfCellOrdinaryIndex z,
      Integrable (fun p : U × ((Fin n → Mom d) × (Fin n → Mom d)) =>
        treeHalfCellCountableCoefficient z β γ a i p*treeHalfCellOrdinaryOp J z i p.2) (μ.prod volume)) ∧
      Summable (fun i : TreeHalfCellOrdinaryIndex z =>
        ∫ p : U × ((Fin n → Mom d) × (Fin n → Mom d)),
          treeHalfCellCountableCoefficient z β γ a i p*treeHalfCellOrdinaryOp J z i p.2 ∂μ.prod volume) := by
  have := isFiniteMeasureOnCompacts_pairs (n := n) (d := d)
  obtain ⟨M,-,hbM⟩ := exists_cellOp_bound hd
  exact tree_countable_bounded_coefficient_factor (μ.prod volume)
    (treeHalfCellCountableCoefficient z β γ a)
    (integrable_treeHalfCellCountableCoefficient μ hn z β γ hβ hγ a ha hi)
    (summable_integral_norm_treeHalfCellCountableCoefficient μ hn z β γ hβ hγ a ha hi hs)
    (fun i p => treeHalfCellOrdinaryOp J z i p.2)
    (fun i => (stronglyMeasurable_treeHalfCellOrdinaryOp hd J z i).comp_measurable measurable_snd)
    (fun i p => norm_treeHalfCellOrdinaryOp_le J (hbM J) z i p.2)

end WaveTurbulence.RA1Leafwise
