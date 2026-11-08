/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FlShell.Shell
/-! # FL-SHELL: the product over trees (`cutWeight2P` as an integral over per-tree scales). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.FlShell
open Finset MeasureTheory Set

/-- The per-tree shell integrand `R⁻¹ ∑_a χD(y_a/R) ∏_{b≠a} χ₀(y_b/R)`, split over the selected `a`. -/
theorem cutWeight2P_eq_integral {w d : ℕ} (LG : LayeredGarden w) (L : ℝ) (hL : 0 < L) (j₂ : ℕ)
    (hj : 0 < j₂) (k : GNode LG.garden.tree → Mom d) :
    LG.cutWeight2P L j₂ k =
      ∫ R in Set.univ.pi (fun _ : Fin w => Set.Icc (2 ^ (j₂ - 1) * L) (2 ^ j₂ * L)),
        ∑ v ∈ Fintype.piFinset (Cases.stemSet LG), ∏ j : Fin w,
          (R j)⁻¹ * (chiD (|omegaNode LG.garden k (v j)| / R j) *
            ∏ b ∈ (Cases.stemSet LG j).erase (v j), chi0 (|omegaNode LG.garden k b| / R j)) := by
  have h1 : ∀ j : Fin w, prodDyadicCut L j₂ (Cases.stemSet LG j)
      (fun b => |omegaNode LG.garden k b|) =
      ∫ R in Set.Icc (2 ^ (j₂ - 1) * L) (2 ^ j₂ * L),
        ∑ a ∈ Cases.stemSet LG j, (R⁻¹ * (chiD (|omegaNode LG.garden k a| / R) *
          ∏ b ∈ (Cases.stemSet LG j).erase a, chi0 (|omegaNode LG.garden k b| / R))) := by
    intro j
    rw [prodDyadicCut_eq_integral L hL j₂ hj, intervalIntegral.integral_of_le
      (XChain.ProductCut.two_pow_pred_le hL j₂), integral_Icc_eq_integral_Ioc]
    simp_rw [Finset.mul_sum]
    congr 1
    funext t
    refine Finset.sum_congr rfl fun a _ => ?_
    congr!
  have h0 : LG.cutWeight2P L j₂ k = ∏ j : Fin w, prodDyadicCut L j₂ (Cases.stemSet LG j)
      (fun b => |omegaNode LG.garden k b|) := rfl
  rw [h0, Finset.prod_congr rfl fun j _ => h1 j]
  have h2 := integral_fintype_prod_eq_prod (𝕜 := ℝ)
    (μ := fun _ : Fin w => volume.restrict (Set.Icc (2 ^ (j₂ - 1) * L) (2 ^ j₂ * L)))
    (fun j (R : ℝ) => ∑ a ∈ Cases.stemSet LG j, (R⁻¹ * (chiD (|omegaNode LG.garden k a| / R) *
          ∏ b ∈ (Cases.stemSet LG j).erase a, chi0 (|omegaNode LG.garden k b| / R))))
  rw [← h2, ← Measure.restrict_pi_pi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun R => ?_)
  simp only
  rw [Finset.prod_univ_sum]
