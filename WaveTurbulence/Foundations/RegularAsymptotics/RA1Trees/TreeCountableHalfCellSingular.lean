/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeHalfCellCountableExpansion

/-! # Actual singular Fubini for the original countable retained half cells -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT

/-- Countable first modulation moments suffice for the actual singular operator to
commute with the complete original half-cell mixture. Every PV convergence and exchange
is supplied by the checked ordinary-cell Fourier representation. -/
theorem tree_singInt_tsum_integral_halfCells {I U : Type*} [Countable I] [MeasurableSpace U]
    (μ : Measure U) [SFinite μ] {d n : ℕ} (hd : 3 ≤ d) (hn : 0 < n) (J : Finset (Fin n))
    (z : I → (Fin n × Fin 2) → Fin d → ℤ)
    (β γ : U → Fin n → Mom d) (hβ : Measurable β) (hγ : Measurable γ)
    (a : I → U → ℂ) (ha : ∀ c, StronglyMeasurable (a c))
    (hi : ∀ c, Integrable (fun u => ‖a c u‖*(1+((∑ j, ‖β u j‖)+(∑ j, ‖γ u j‖)))) μ)
    (hs : Summable (fun c => ∫ u, ‖a c u‖*(1+((∑ j, ‖β u j‖)+(∑ j, ‖γ u j‖))) ∂μ)) :
    singInt J (fun x y => ∑' c, ∫ u, a c u*halfCellAmplitude (z c) (β u) (γ u) x y ∂μ) =
      ∑' c, ∫ u, a c u*singInt J (halfCellAmplitude (z c) (β u) (γ u)) ∂μ := by
  have hkernel : treeHalfCellCountableKernel μ z β γ a =
      (fun x y => ∑' c, ∫ u, a c u*halfCellAmplitude (z c) (β u) (γ u) x y ∂μ) := by
    funext x y
    have hFn := (tree_halfCell_countableFn_integrable_summable μ hn z β γ hβ hγ a ha hi hs x y).2
    rw [treeHalfCellCountableKernel,hFn.tsum_sigma]
    apply tsum_congr
    intro c
    rw [tsum_fintype]
    exact (tree_halfCell_integral_eq_ordinary_cells μ hn z β γ hβ hγ a ha hi hs c x y).symm
  have he := singInt_treeHalfCellCountableKernel_eq μ hd hn J z β γ hβ hγ a ha hi hs
  rw [hkernel] at he
  have hOp := (tree_halfCell_countableOp_integrable_summable μ hd hn J z β γ hβ hγ a ha hi hs).2
  rw [hOp.tsum_sigma] at he
  simp_rw [tsum_fintype] at he
  exact he.trans (tsum_congr (fun c => tree_halfCell_ordinary_ops_eq_integral μ hn z β γ hβ hγ a ha hi hs hd J c))

end WaveTurbulence.RegAsymp
