/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepNode2
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the mass of the joint index with node centres
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic
open scoped ENNReal

variable {w d : ℕ} {S : Garden w}

open scoped Classical in
theorem mass_node_le (fam : SlotFam S d) (hS : S.IsPlain) :
    ∑' p : (∀ s, fam.Λ s) × (GBranch S.tree → Fin d → ℤ),
      ENNReal.ofReal ((∏ s, fam.w s (p.1 s)) *
        (if p.2 ∈ nodeCentreSet (fam.leafCentre hS p.1) then 1 else 0)) ≤
      (∏ s, ∑' l, ENNReal.ofReal (fam.w s l)) *
        ((nodeBallCard d ^ ∑ j, (S.tree j).order : ℕ) : ℝ≥0∞) := by
  rw [ENNReal.tsum_prod (f := fun (ξ : ∀ s, fam.Λ s) (x : GBranch S.tree → Fin d → ℤ) =>
    ENNReal.ofReal ((∏ s, fam.w s (ξ s)) *
      (if x ∈ nodeCentreSet (fam.leafCentre hS ξ) then 1 else 0)))]
  have hfib : ∀ ξ : ∀ s, fam.Λ s, ∑' x : GBranch S.tree → Fin d → ℤ,
      ENNReal.ofReal ((∏ s, fam.w s (ξ s)) *
        (if x ∈ nodeCentreSet (fam.leafCentre hS ξ) then 1 else 0)) ≤
      ENNReal.ofReal (∏ s, fam.w s (ξ s)) * ((nodeBallCard d ^ ∑ j, (S.tree j).order : ℕ) : ℝ≥0∞) := by
    intro ξ
    obtain ⟨hF, hC⟩ := nodeCentreSet_finite_card (fam.leafCentre hS ξ)
    have h1 : ∀ x : GBranch S.tree → Fin d → ℤ,
        ENNReal.ofReal ((∏ s, fam.w s (ξ s)) *
          (if x ∈ nodeCentreSet (fam.leafCentre hS ξ) then 1 else 0)) =
        if x ∈ hF.toFinset then ENNReal.ofReal (∏ s, fam.w s (ξ s)) else 0 := by
      intro x
      by_cases hx : x ∈ nodeCentreSet (fam.leafCentre hS ξ)
      · simp [hx, (Set.Finite.mem_toFinset hF).2 hx]
      · have : x ∉ hF.toFinset := fun h => hx ((Set.Finite.mem_toFinset hF).1 h)
        simp [hx, this]
    simp_rw [h1]
    rw [tsum_eq_sum (s := hF.toFinset) (fun x hx => by simp [hx])]
    rw [Finset.sum_ite_of_true (fun x hx => hx), Finset.sum_const, nsmul_eq_mul]
    have hcard : (hF.toFinset.card : ℝ≥0∞) ≤ ((nodeBallCard d ^ ∑ j, (S.tree j).order : ℕ) : ℝ≥0∞) := by
      rw [← Set.ncard_eq_toFinset_card _ hF]
      exact_mod_cast hC
    calc (hF.toFinset.card : ℝ≥0∞) * ENNReal.ofReal (∏ s, fam.w s (ξ s))
        = ENNReal.ofReal (∏ s, fam.w s (ξ s)) * (hF.toFinset.card : ℝ≥0∞) := mul_comm _ _
      _ ≤ _ := by gcongr
  calc ∑' ξ : ∀ s, fam.Λ s, ∑' x : GBranch S.tree → Fin d → ℤ,
        ENNReal.ofReal ((∏ s, fam.w s (ξ s)) *
          (if x ∈ nodeCentreSet (fam.leafCentre hS ξ) then 1 else 0))
      ≤ ∑' ξ : ∀ s, fam.Λ s, ENNReal.ofReal (∏ s, fam.w s (ξ s)) *
          ((nodeBallCard d ^ ∑ j, (S.tree j).order : ℕ) : ℝ≥0∞) := ENNReal.tsum_le_tsum hfib
    _ = (∑' ξ : ∀ s, fam.Λ s, ENNReal.ofReal (∏ s, fam.w s (ξ s))) *
          ((nodeBallCard d ^ ∑ j, (S.tree j).order : ℕ) : ℝ≥0∞) := ENNReal.tsum_mul_right
    _ = _ := by rw [tsum_ofReal_prod_fintype fam.w fam.w_nn]

end WaveTurbulence.Represents
