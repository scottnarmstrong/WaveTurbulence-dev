/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm9
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the total absolute mass of the assembled summand is finite
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  WaveTurbulence.VineEstS3.FS MeasureTheory Set
open scoped ENNReal

variable {w d : ℕ} {S : Garden w} (A : AsmCtx S d)

theorem AsmCtx.lintegral_gI_le (ξ : XiT A.fam) (κ : GenDecoration S d A.roots 0) :
    ∫⁻ τ, ‖A.gI ξ κ τ‖ₑ ≤
      ENNReal.ofReal (‖constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖ * ‖A.E ξ κ‖) := by
  classical
  set c : ℝ := ‖constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖ * ‖A.E ξ κ‖ with hc
  have hc0 : 0 ≤ c := by positivity
  calc ∫⁻ τ, ‖A.gI ξ κ τ‖ₑ
      ≤ ∫⁻ τ, (splicedTimeDomain S A.layer0 A.tt).indicator (fun _ => ENNReal.ofReal c) τ := by
        refine lintegral_mono fun τ => ?_
        have := A.norm_gI_le ξ κ τ
        by_cases hτ : τ ∈ splicedTimeDomain S A.layer0 A.tt
        · simp only [Set.indicator_of_mem hτ] at this ⊢
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal this
        · simp only [Set.indicator_of_notMem hτ] at this ⊢
          have h0 : A.gI ξ κ τ = 0 := norm_le_zero_iff.1 this
          rw [h0]; simp
    _ = ENNReal.ofReal c * volume (splicedTimeDomain S A.layer0 A.tt) :=
        lintegral_indicator_const (measurableSet_splicedTimeDomain S A.layer0 A.tt) _
    _ ≤ ENNReal.ofReal c * 1 := by
        gcongr; exact volume_splicedTimeDomain_le _ _ _
    _ = _ := mul_one _

open scoped Classical in
theorem AsmCtx.tsum_bondProd_le (ξ : XiT A.fam) :
    ∑' κ : GenDecoration S d A.roots 0, ENNReal.ofReal ‖A.E ξ κ‖ ≤
      (((⌊2 * A.L⌋₊ + 2) ^ d) ^ Fintype.card (SourcePair S) : ℕ) := by
  obtain ⟨hF, hC⟩ := decoration_count A.hS A.L A.hL A.base A.roots (cenS A.fam ξ)
  set K := {κ : GenDecoration S d A.roots 0 |
    ∀ s, hasBond A.hS s → ‖A.base + latticePoint A.L (κ.1 (slotNode A.hS s)) - cenS A.fam ξ s‖ ≤ 1} with hK
  have hle : ∀ κ : GenDecoration S d A.roots 0, ENNReal.ofReal ‖A.E ξ κ‖ ≤
      if κ ∈ hF.toFinset then 1 else 0 := by
    intro κ
    by_cases hκ : κ ∈ hF.toFinset
    · simp only [hκ, ite_true]
      have := norm_bondProd_le A.fam A.hS A.hd A.Cχ A.hC A.hCpos A.L A.base κ.1 ξ
      calc ENNReal.ofReal ‖A.E ξ κ‖ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal this
        _ = 1 := ENNReal.ofReal_one
    · simp only [hκ, ite_false, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero]
      by_contra hne
      push Not at hne
      apply hκ
      rw [Set.Finite.mem_toFinset]
      have hne' : A.E ξ κ ≠ 0 := fun h0 => by simp [h0] at hne
      exact bondProd_ne_zero_support A.fam A.hS A.Cχ A.L A.base κ.1 κ.2.1.2 ξ hne'
  calc ∑' κ : GenDecoration S d A.roots 0, ENNReal.ofReal ‖A.E ξ κ‖
      ≤ ∑' κ : GenDecoration S d A.roots 0, (if κ ∈ hF.toFinset then (1 : ℝ≥0∞) else 0) :=
        ENNReal.tsum_le_tsum hle
    _ = ((hF.toFinset.card : ℕ) : ℝ≥0∞) := by
        rw [tsum_eq_sum (s := hF.toFinset) (fun x hx => by simp [hx]), Finset.sum_ite_of_true (fun x hx => hx),
          Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ _ := by
        have : hF.toFinset.card ≤ ((⌊2 * A.L⌋₊ + 2) ^ d) ^ Fintype.card (SourcePair S) := by
          rw [← Set.ncard_eq_toFinset_card _ hF]; exact hC
        exact_mod_cast this

open scoped Classical in
theorem AsmCtx.tsum_constW_le :
    ∑' ξ : XiT A.fam, ENNReal.ofReal ‖constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖ ≤
      ENNReal.ofReal (A.Cχ ^ (Fintype.card (GBranch S.tree))) *
        ((∏ s, ∑' l, ENNReal.ofReal (A.fam.w s l)) *
          ((nodeBallCard d ^ ∑ j, (S.tree j).order : ℕ) : ℝ≥0∞)) := by
  calc ∑' ξ : XiT A.fam, ENNReal.ofReal ‖constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖
      ≤ ∑' ξ : XiT A.fam, ENNReal.ofReal (A.Cχ ^ (Fintype.card (GBranch S.tree))) *
          ENNReal.ofReal ((∏ s, A.fam.w s (ξ.1 s)) *
            (if ξ.2 ∈ nodeCentreSet (A.fam.leafCentre A.hS ξ.1) then 1 else 0)) := by
        refine ENNReal.tsum_le_tsum fun ξ => ?_
        rw [← ENNReal.ofReal_mul (pow_nonneg A.hCpos.le _)]
        exact ENNReal.ofReal_le_ofReal
          (norm_constW_le A.fam A.hS A.hd A.Cχ A.hC A.hCpos A.L A.base A.roots A.tt ξ)
    _ = ENNReal.ofReal (A.Cχ ^ (Fintype.card (GBranch S.tree))) *
          ∑' ξ : XiT A.fam, ENNReal.ofReal ((∏ s, A.fam.w s (ξ.1 s)) *
            (if ξ.2 ∈ nodeCentreSet (A.fam.leafCentre A.hS ξ.1) then 1 else 0)) := ENNReal.tsum_mul_left
    _ ≤ _ := by gcongr; exact mass_node_le A.fam A.hS

theorem AsmCtx.mass_ne_top : (∏ s, ∑' l, ENNReal.ofReal (A.fam.w s l)) ≠ ⊤ := by
  refine ENNReal.prod_ne_top fun s _ => ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (A.fam.w_nn s) (A.fam.w_sum s)]
  exact ENNReal.ofReal_ne_top

open scoped Classical in
theorem AsmCtx.sum_lintegral_ne_top :
    ∑' ξ : XiT A.fam, ∑' κ : GenDecoration S d A.roots 0, ∫⁻ τ, ‖A.gI ξ κ τ‖ₑ ≠ ⊤ := by
  set N : ℝ≥0∞ := ((((⌊2 * A.L⌋₊ + 2) ^ d) ^ Fintype.card (SourcePair S) : ℕ) : ℝ≥0∞) with hN
  have h1 : ∑' ξ : XiT A.fam, ∑' κ : GenDecoration S d A.roots 0, ∫⁻ τ, ‖A.gI ξ κ τ‖ₑ ≤
      ∑' ξ : XiT A.fam, ENNReal.ofReal ‖constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖ * N := by
    refine ENNReal.tsum_le_tsum fun ξ => ?_
    calc ∑' κ : GenDecoration S d A.roots 0, ∫⁻ τ, ‖A.gI ξ κ τ‖ₑ
        ≤ ∑' κ : GenDecoration S d A.roots 0,
            ENNReal.ofReal ‖constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖ *
              ENNReal.ofReal ‖A.E ξ κ‖ := by
          refine ENNReal.tsum_le_tsum fun κ => ?_
          refine (A.lintegral_gI_le ξ κ).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_mul (norm_nonneg _)]
      _ = ENNReal.ofReal ‖constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖ *
            ∑' κ : GenDecoration S d A.roots 0, ENNReal.ofReal ‖A.E ξ κ‖ := ENNReal.tsum_mul_left
      _ ≤ _ := by gcongr; exact A.tsum_bondProd_le ξ
  refine ne_top_of_le_ne_top ?_ h1
  rw [ENNReal.tsum_mul_right]
  refine ENNReal.mul_ne_top (ne_top_of_le_ne_top ?_ A.tsum_constW_le) (by simp [hN])
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top A.mass_ne_top (by simp))

end WaveTurbulence.Represents
