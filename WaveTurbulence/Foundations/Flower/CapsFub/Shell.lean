/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FlShell.Product
public import WaveTurbulence.Foundations.Flower.MkAsm.Helpers
public import WaveTurbulence.Foundations.Flower.Fam.Prof2
/-! # CAPS-FUBINI: the shell integrand, its measurability and its bound on the shell box. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsFub
open Finset MeasureTheory Set WaveTurbulence.Flower.FlShell

/-- The integrand of `FlShell.cutWeight2P_eq_integral`. -/
def shellIntegrand {w d : ℕ} (LG : LayeredGarden w) (L : ℝ) (k : GNode LG.garden.tree → Mom d)
    (R : Fin w → ℝ) : ℝ :=
  ∑ v ∈ Fintype.piFinset (Cases.stemSet LG), ∏ j : Fin w,
    (R j)⁻¹ * (chiD (|omegaNode LG.garden k (v j)| / R j) *
      ∏ b ∈ (Cases.stemSet LG j).erase (v j), chi0 (|omegaNode LG.garden k b| / R j))

theorem cutWeight2P_eq_shellIntegrand {w d : ℕ} (LG : LayeredGarden w) (L : ℝ) (hL : 0 < L) (j₂ : ℕ)
    (hj : 0 < j₂) (k : GNode LG.garden.tree → Mom d) :
    LG.cutWeight2P L j₂ k = ∫ R in MkAsm.shellBox w L j₂, shellIntegrand LG L k R :=
  cutWeight2P_eq_integral LG L hL j₂ hj k

theorem measurable_shellIntegrand {w d : ℕ} (LG : LayeredGarden w) (L : ℝ)
    (k : GNode LG.garden.tree → Mom d) : Measurable (shellIntegrand LG L k) := by
  unfold shellIntegrand
  refine Finset.measurable_sum _ fun v _ => Finset.measurable_prod _ fun j _ => ?_
  have hR : Measurable fun R : Fin w → ℝ => R j := measurable_pi_apply j
  refine hR.inv.mul (Measurable.mul ?_ ?_)
  · exact continuous_chiD.measurable.comp (measurable_const.div hR)
  · exact Finset.measurable_prod _ fun b _ =>
      (chi0_contDiff.continuous.measurable).comp (measurable_const.div hR)

theorem exists_abs_chiD_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ u, |chiD u| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    continuous_chiD.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun u => ?_⟩
  by_cases hu : u ∈ Icc (-1 : ℝ) 1
  · exact (by simpa using hC u hu : |chiD u| ≤ C).trans (le_max_left _ _)
  · have : chiD u = 0 := by
      by_contra h
      have := (chiD_support h).2
      exact hu ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
    rw [this]; simp

theorem abs_shellIntegrand_le {w d : ℕ} (LG : LayeredGarden w) (L : ℝ) (hL : 0 < L) (j₂ : ℕ)
    (k : GNode LG.garden.tree → Mom d) (Cd : ℝ) (hCd : ∀ u, |chiD u| ≤ Cd) (R : Fin w → ℝ)
    (hR : R ∈ MkAsm.shellBox w L j₂) :
    |shellIntegrand LG L k R| ≤
      ((Fintype.piFinset (Cases.stemSet LG)).card : ℝ) * ((2 ^ (j₂ - 1) * L)⁻¹ * Cd) ^ w := by
  have hRj : ∀ j, 2 ^ (j₂ - 1) * L ≤ R j := fun j => (hR j (mem_univ j)).1
  have hapos : 0 < 2 ^ (j₂ - 1) * L := by positivity
  unfold shellIntegrand
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (((2 ^ (j₂ - 1) * L)⁻¹ * Cd) ^ w) fun v _ => ?_).trans_eq
    (nsmul_eq_mul _ _)
  rw [Finset.abs_prod]
  calc ∏ j : Fin w, |(R j)⁻¹ * (chiD (|omegaNode LG.garden k (v j)| / R j) *
          ∏ b ∈ (Cases.stemSet LG j).erase (v j), chi0 (|omegaNode LG.garden k b| / R j))|
      ≤ ∏ _j : Fin w, ((2 ^ (j₂ - 1) * L)⁻¹ * Cd) := by
        refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun j _ => ?_
        have hRpos : 0 < R j := hapos.trans_le (hRj j)
        rw [abs_mul, abs_mul, abs_inv, abs_of_pos hRpos]
        have h1 : (R j)⁻¹ ≤ (2 ^ (j₂ - 1) * L)⁻¹ := inv_anti₀ hapos (hRj j)
        have h2 : |∏ b ∈ (Cases.stemSet LG j).erase (v j), chi0 (|omegaNode LG.garden k b| / R j)| ≤ 1 := by
          rw [Finset.abs_prod]
          refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun b _ => ?_
          rw [abs_of_nonneg (XChain.ProductCut.chi0_nonneg _)]
          exact XChain.ProductCut.chi0_le_one _
        have h3 : |chiD (|omegaNode LG.garden k (v j)| / R j)| *
            |∏ b ∈ (Cases.stemSet LG j).erase (v j), chi0 (|omegaNode LG.garden k b| / R j)| ≤ Cd := by
          calc _ ≤ Cd * 1 := mul_le_mul (hCd _) h2 (abs_nonneg _) ((abs_nonneg _).trans (hCd 0))
            _ = Cd := mul_one _
        exact mul_le_mul h1 h3 (by positivity) (inv_nonneg.2 hapos.le)
    _ = _ := by simp

end WaveTurbulence.Flower.CapsFub
