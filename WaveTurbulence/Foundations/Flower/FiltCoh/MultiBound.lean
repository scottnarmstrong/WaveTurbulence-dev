/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.MultiSplit

/-! # FILT-COH (c5): uniform bounds of the D5 multiplier

`chiDSup` bounds FL-SHELL's annular factor `chiD` (continuous, supported in `1/2 < |u| < 1`); `norm_filtWeight_le`
and `norm_d5Mult_le` give the uniform bound of the D5 multiplier, used for the summability in `coupleW_split` /
`treeW_split` and for the time continuity of multiplied kernels. -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open MeasureTheory Set Finset
open scoped ENNReal

theorem exists_chiD_sup : ∃ C : ℝ, 1 ≤ C ∧ ∀ u : ℝ, |FlShell.chiD u| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
    FlShell.continuous_chiD.continuousOn
  refine ⟨max C 1, le_max_right _ _, fun u => ?_⟩
  by_cases hu : u ∈ Icc (-1 : ℝ) 1
  · exact (by simpa only [Real.norm_eq_abs] using hC u hu : |FlShell.chiD u| ≤ C).trans (le_max_left _ _)
  · have h0 : FlShell.chiD u = 0 := by
      by_contra h
      have hs := FlShell.chiD_support h
      exact hu ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
    rw [h0, abs_zero]
    exact zero_le_one.trans (le_max_right _ _)

/-- A uniform bound of the annular factor (at least one). -/
@[expose] def chiDSup : ℝ := Classical.choose exists_chiD_sup

theorem one_le_chiDSup : 1 ≤ chiDSup := (Classical.choose_spec exists_chiD_sup).1

theorem abs_chiD_le_sup (u : ℝ) : |FlShell.chiD u| ≤ chiDSup := (Classical.choose_spec exists_chiD_sup).2 u

theorem norm_filtWeight_le {w d : ℕ} {G : Garden w} (F : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool)
    (M : GBranch G.tree → ℝ) (κ : GNode G.tree → Mom d) :
    ‖ProtDefs.filtWeight F ann M κ‖ ≤ chiDSup ^ F.card := by
  unfold ProtDefs.filtWeight
  rw [norm_prod]
  refine (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun b _ => ?_).trans_eq (Finset.prod_const _)
  rw [Complex.norm_real, Real.norm_eq_abs]
  split_ifs
  · exact abs_chiD_le_sup _
  · rw [abs_of_nonneg (XChain.ProductCut.chi0_nonneg _)]
    exact (XChain.ProductCut.chi0_le_one _).trans one_le_chiDSup

/-- **The D5 multiplier is uniformly bounded.** -/
theorem norm_d5Mult_le {J w d : ℕ} {G : Garden w} (S : Finset (GNode G.tree))
    (ω : GNode G.tree → IncTop.Star d → ℂ) (c : GNode G.tree → ℝ)
    (h : ∀ a ∈ S, IncTop.StarPresented J (ω a) (c a)) (F : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool)
    (M : GBranch G.tree → ℝ) (Fu : Finset (GBranch G.tree)) (Mu : GBranch G.tree → ℝ) (κ : GNode G.tree → Mom d) :
    ‖d5Mult S ω F ann M Fu Mu κ‖ ≤ (∏ a ∈ S, max (c a) 0) * chiDSup ^ F.card * chiDSup ^ Fu.card := by
  unfold d5Mult
  rw [norm_mul, norm_mul]
  have h1 := norm_starWeight_le S ω c h κ
  have h2 := norm_filtWeight_le F ann M κ
  have h3 := norm_filtWeight_le Fu (fun _ => false) Mu κ
  have hp : 0 ≤ ∏ a ∈ S, max (c a) 0 := Finset.prod_nonneg fun _ _ => le_max_right _ _
  have hc : 0 ≤ chiDSup ^ F.card := pow_nonneg (zero_le_one.trans one_le_chiDSup) _
  exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hp) h3 (norm_nonneg _) (mul_nonneg hp hc)

section Mem

variable {w : ℕ} [NeZero w] {G : Garden w} {G₁ : Garden 1} {G₂ : Garden w} {X : RegChain}
  (h : PL234.GlueData G G₁ G₂ X)

theorem mem_starTop {S : Finset (GNode G.tree)} {x : GNode G₁.tree} (hx : x ∈ starTop h S) : h.ι₁ x ∈ S := by
  classical
  simp only [starTop, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact hx.1

theorem mem_starBot {S : Finset (GNode G.tree)} {y : GNode G₂.tree} (hy : y ∈ starBot h S) : h.ι₂ y ∈ S := by
  classical
  simp only [starBot, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  exact hy

end Mem

/-- Leaf profiles enter the multiplied kernel only through the input leaves. -/
theorem kernelLeavesW_congr_H' {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H H' : LGSpine.LeafProfiles w d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, H ℓ.1 = H' ℓ.1)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) :
    Flower.Stage1W.kernelLeavesW L γ δ LG H up s k₀ nroot nfl m =
      Flower.Stage1W.kernelLeavesW L γ δ LG H' up s k₀ nroot nfl m := by
  unfold Flower.Stage1W.kernelLeavesW
  congr 1
  refine tsum_congr fun κ => ?_
  congr 2
  exact Finset.prod_congr rfl fun ℓ hℓ => by rw [hH ℓ hℓ]

end WaveTurbulence.Flower.FiltCoh
