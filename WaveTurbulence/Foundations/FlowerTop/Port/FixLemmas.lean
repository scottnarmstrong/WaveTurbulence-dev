/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.SplicedKernelST
/-! # FLOWER-P5: basic facts on the designated-time extension `Garden.extendFix` -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP5
open WaveTurbulence WaveTurbulence.LGSpine MeasureTheory Set Finset
open scoped Classical

variable {w d : ℕ} {G : Garden w}

theorem extendFix_free (fix : GBranch G.tree → Option ℝ) (τ : {b : GBranch G.tree // fix b = none} → ℝ)
    (b : GBranch G.tree) (h : fix b = none) : G.extendFix fix τ b = τ ⟨b, h⟩ := by
  unfold Garden.extendFix
  split
  · rename_i v hv; rw [h] at hv; cases hv
  · rename_i hv; rfl

theorem continuous_extendFix (fix : GBranch G.tree → Option ℝ) :
    Continuous (G.extendFix fix) := by
  refine continuous_pi fun b => ?_
  unfold Garden.extendFix
  by_cases h : fix b = none
  · have : (fun τ : {b : GBranch G.tree // fix b = none} → ℝ => G.extendFix fix τ b) =
        fun τ => τ ⟨b, h⟩ := funext fun τ => extendFix_free fix τ b h
    show Continuous (fun τ => G.extendFix fix τ b)
    rw [this]; exact continuous_apply _
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h
    have : (fun τ : {b : GBranch G.tree // fix b = none} → ℝ => G.extendFix fix τ b) = fun _ => v := by
      funext τ; unfold Garden.extendFix; split
      · rename_i v' hv'; rw [hv] at hv'; cases hv'; rfl
      · rename_i hv'; rw [hv] at hv'; cases hv'
    show Continuous (fun τ => G.extendFix fix τ b)
    rw [this]; exact continuous_const

theorem measurable_extendFix (fix : GBranch G.tree → Option ℝ) : Measurable (G.extendFix fix) :=
  (continuous_extendFix fix).measurable

theorem measurableSet_splicedTimeDomainFix (G : Garden w) (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) : MeasurableSet (splicedTimeDomainFix G layer rootTime fix) := by
  unfold splicedTimeDomainFix
  have h1 : ∀ v : GBranch G.tree, MeasurableSet {t : GBranch G.tree → ℝ |
      fix v = none → (t v ∈ Icc (layer v : ℝ) (layer v + 1) ∧ t v < rootTime v.1.1)} := by
    intro v
    by_cases h : fix v = none
    · simp only [h, forall_const]; measurability
    · simp only [h, false_imp_iff, Set.ofPred_true]; exact MeasurableSet.univ
  have h2 : ∀ v u : GBranch G.tree, MeasurableSet {t : GBranch G.tree → ℝ |
      v.IsChildOf u → (fix v = none ∨ fix u = none) → t v < t u} := by
    intro v u
    by_cases h : v.IsChildOf u ∧ (fix v = none ∨ fix u = none)
    · simp only [h.1, h.2, forall_true_left]
      exact measurableSet_lt (measurable_pi_apply v) (measurable_pi_apply u)
    · have : {t : GBranch G.tree → ℝ | v.IsChildOf u → (fix v = none ∨ fix u = none) → t v < t u} = univ := by
        ext t; simp only [mem_ofPred_eq, mem_univ, iff_true]; intro a b; exact absurd ⟨a, b⟩ h
      rw [this]; exact MeasurableSet.univ
  have : {t : GBranch G.tree → ℝ | (∀ v, fix v = none → t v ∈ Icc (layer v : ℝ) (layer v + 1) ∧ t v < rootTime v.1.1) ∧
      ∀ v u, v.IsChildOf u → (fix v = none ∨ fix u = none) → t v < t u} =
      (⋂ v, {t : GBranch G.tree → ℝ | fix v = none → (t v ∈ Icc (layer v : ℝ) (layer v + 1) ∧ t v < rootTime v.1.1)}) ∩
      ⋂ v, ⋂ u, {t : GBranch G.tree → ℝ | v.IsChildOf u → (fix v = none ∨ fix u = none) → t v < t u} := by
    ext t; simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [this]
  exact (MeasurableSet.iInter h1).inter (MeasurableSet.iInter fun v => MeasurableSet.iInter (h2 v))

end WaveTurbulence.FlowerP5
