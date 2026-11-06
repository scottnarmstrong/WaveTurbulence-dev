/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.GenBridge3
import Mathlib.Tactic
/-! `Phi` of the literal class domain equals `Bprod` of the product model, and the resulting
`α`-integral bound from `core1`. -/
@[expose] public section
open MeasureTheory Set Finset Function
open scoped ENNReal
namespace WaveTurbulence.Ladder
open scoped Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k m : ℕ}

theorem measurableSet_Rmod (ls cap : ι → ℝ) (lt le : ι → ι → Prop) (xv : Fin k → ι)
    (Rv : Set (Fin k → ℝ)) (hRv : MeasurableSet Rv) : MeasurableSet (Rmod ls cap lt le xv Rv) := by
  unfold Rmod
  refine hRv.inter ?_
  have e1 : MeasurableSet {tx : Fin k → ℝ | ∀ i, tx i ∈ Icc (ls (xv i)) (ls (xv i) + 1)} := by
    have : {tx : Fin k → ℝ | ∀ i, tx i ∈ Icc (ls (xv i)) (ls (xv i) + 1)} =
        ⋂ i, (fun t : Fin k → ℝ => t i) ⁻¹' Icc (ls (xv i)) (ls (xv i) + 1) := by ext t; simp
    rw [this]
    exact MeasurableSet.iInter (fun v => measurableSet_Icc.preimage (measurable_pi_apply v))
  have e2c : MeasurableSet {tx : Fin k → ℝ | ∀ i, tx i < cap (xv i)} := by
    have : {tx : Fin k → ℝ | ∀ i, tx i < cap (xv i)} = ⋂ i, {tx : Fin k → ℝ | tx i < cap (xv i)} := by ext t; simp
    rw [this]
    exact MeasurableSet.iInter (fun v => measurableSet_lt (measurable_pi_apply v) measurable_const)
  have e2 : MeasurableSet {tx : Fin k → ℝ | ∀ i i', lt (xv i) (xv i') → tx i < tx i'} := by
    have : {tx : Fin k → ℝ | ∀ i i', lt (xv i) (xv i') → tx i < tx i'} =
        ⋂ a, ⋂ b, {tx : Fin k → ℝ | lt (xv a) (xv b) → tx a < tx b} := by ext t; simp
    rw [this]
    refine MeasurableSet.iInter (fun a => MeasurableSet.iInter (fun b => ?_))
    by_cases h : lt (xv a) (xv b)
    · simp only [h, true_implies]
      exact measurableSet_lt (measurable_pi_apply a) (measurable_pi_apply b)
    · simp [h]
  have e3 : MeasurableSet {tx : Fin k → ℝ | ∀ i i', le (xv i) (xv i') → tx i ≤ tx i'} := by
    have : {tx : Fin k → ℝ | ∀ i i', le (xv i) (xv i') → tx i ≤ tx i'} =
        ⋂ a, ⋂ b, {tx : Fin k → ℝ | le (xv a) (xv b) → tx a ≤ tx b} := by ext t; simp
    rw [this]
    refine MeasurableSet.iInter (fun a => MeasurableSet.iInter (fun b => ?_))
    by_cases h : le (xv a) (xv b)
    · simp only [h, true_implies]
      exact measurableSet_le (measurable_pi_apply a) (measurable_pi_apply b)
    · simp [h]
  exact e1.inter (e2c.inter (e2.inter e3))

theorem Phi_eq_Bprod (e : ι ≃ Fin k ⊕ Fin m) (ls cap : ι → ℝ) (lt le : ι → ι → Prop)
    (Rv : Set (Fin k → ℝ)) (hRv : MeasurableSet Rv) (par : Par m)
    (hpar : ∀ j j', par j = some j' ↔ lt (e.symm (Sum.inr j)) (e.symm (Sum.inr j')))
    (hle : ∀ j j', ¬ le (e.symm (Sum.inr j)) (e.symm (Sum.inr j')))
    (A : Finset ι) (α : ι → ℝ) :
    Phi (OmegaC ls cap lt le (fun i => e.symm (Sum.inl i)) Rv) ls A α =
      Bprod par (fun j => ls (e.symm (Sum.inr j))) (fun j => decide (e.symm (Sum.inr j) ∈ A))
        (loF (fun j => ls (e.symm (Sum.inr j))) (LBf lt le (fun i => e.symm (Sum.inl i)) (fun j => e.symm (Sum.inr j))))
        (hiF (fun j => ls (e.symm (Sum.inr j))) (fun j => cap (e.symm (Sum.inr j))) (UBf lt le (fun i => e.symm (Sum.inl i)) (fun j => e.symm (Sum.inr j))))
        (Rmod ls cap lt le (fun i => e.symm (Sum.inl i)) Rv) (wXf e ls A) (Th e α) := by
  set Ω := OmegaC ls cap lt le (fun i => e.symm (Sum.inl i)) Rv with hΩ
  set M := Mset ls cap lt le (fun i => e.symm (Sum.inl i)) (fun j => e.symm (Sum.inr j)) Rv par with hM
  set g : (Fin k → ℝ) × (Fin m → ℝ) → ℂ := fun p => famInt ls A α ((Th e).symm p) with hg
  set G : (Fin k → ℝ) × (Fin m → ℝ) → ℂ := M.indicator g with hG
  have hae := ae_eq_Mset e ls cap lt le Rv par hpar hle
  have hGt : ∀ t, G (Th e t) = ((Th e) ⁻¹' M).indicator (famInt ls A α) t := by
    intro t
    simp only [hG, hg, Set.indicator_apply, Set.mem_preimage, MeasurableEquiv.symm_apply_apply]
  have hΩm := measurableSet_OmegaC ls cap lt le (fun i => e.symm (Sum.inl i)) Rv hRv
  have hint0 := integrable_indicator_famInt Ω hΩm _ (bdd_OmegaC ls cap lt le _ Rv) ls A α
  have hintG : Integrable G := by
    rw [← (Th_mp e).integrable_comp_emb (Th e).measurableEmbedding]
    have : (G ∘ Th e) =ᵐ[volume] Ω.indicator (famInt ls A α) := by
      have h2 := indicator_ae_eq_of_ae_eq_set (f := famInt ls A α) hae
      filter_upwards [h2] with t ht
      rw [Function.comp_apply, hGt, ht]
    exact hint0.congr this.symm
  have step1 : Phi Ω ls A α = ∫ p, G p := by
    unfold Phi
    have h2 := indicator_ae_eq_of_ae_eq_set (f := famInt ls A α) hae
    rw [integral_congr_ae h2]
    rw [← (Th_mp e).integral_comp' G]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun t => (hGt t).symm))
  rw [step1, Measure.volume_eq_prod, integral_prod _ (by rwa [← Measure.volume_eq_prod])]
  have hRm : MeasurableSet (Rmod ls cap lt le (fun i => e.symm (Sum.inl i)) Rv) :=
    measurableSet_Rmod ls cap lt le _ Rv hRv
  set F : (Fin k → ℝ) → (Fin m → ℝ) → ℂ := fun tx ty => wXf e ls A tx *
        ((∏ i, ee (Real.pi * (Th e α).1 i) (tx i)) *
        ((∏ j, if (decide (e.symm (Sum.inr j) ∈ A)) = true then
            (((ty j - ls (e.symm (Sum.inr j)) : ℝ)) : ℂ) else 1) *
          Fd par (loF (fun j => ls (e.symm (Sum.inr j))) (LBf lt le (fun i => e.symm (Sum.inl i)) (fun j => e.symm (Sum.inr j))) tx)
            (hiF (fun j => ls (e.symm (Sum.inr j))) (fun j => cap (e.symm (Sum.inr j))) (UBf lt le (fun i => e.symm (Sum.inl i)) (fun j => e.symm (Sum.inr j))) tx)
            (Real.pi • (Th e α).2) ty)) with hF
  have hpt : ∀ (tx : Fin k → ℝ) (ty : Fin m → ℝ), G (tx, ty) =
      (Rmod ls cap lt le (fun i => e.symm (Sum.inl i)) Rv).indicator (fun tx => F tx ty) tx := by
    intro tx ty
    by_cases hR : tx ∈ Rmod ls cap lt le (fun i => e.symm (Sum.inl i)) Rv
    · rw [Set.indicator_of_mem hR]
      simp only [hF]
      rw [Fd_eq]
      by_cases hc : (∀ j, ty j ∈ Ioc (loF (fun j => ls (e.symm (Sum.inr j))) (LBf lt le (fun i => e.symm (Sum.inl i)) (fun j => e.symm (Sum.inr j))) tx j)
            (hiF (fun j => ls (e.symm (Sum.inr j))) (fun j => cap (e.symm (Sum.inr j))) (UBf lt le (fun i => e.symm (Sum.inl i)) (fun j => e.symm (Sum.inr j))) tx j)) ∧
          (∀ j j', par j = some j' → ty j < ty j')
      · have hmem : (tx, ty) ∈ M := ⟨hR, hc.1, hc.2⟩
        rw [hG, Set.indicator_of_mem hmem, hg]
        simp only [famInt_symm, if_pos hc]
        simp only [decide_eq_true_eq]; ring
      · have hmem : (tx, ty) ∉ M := fun h => hc ⟨h.2.1, h.2.2⟩
        rw [hG, Set.indicator_of_notMem hmem]
        simp only [if_neg hc]; simp
    · rw [Set.indicator_of_notMem hR]
      have hmem : (tx, ty) ∉ M := fun h => hR h.1
      rw [hG, Set.indicator_of_notMem hmem]
  unfold Bprod
  rw [← integral_indicator hRm]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun tx => ?_))
  simp only [hpt]
  by_cases hR : tx ∈ Rmod ls cap lt le (fun i => e.symm (Sum.inl i)) Rv
  · simp only [Set.indicator_of_mem hR]
    unfold Uintw
    rw [integral_const_mul, integral_const_mul]
  · simp [Set.indicator_of_notMem hR]

end WaveTurbulence.Ladder
