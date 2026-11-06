/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib
/-! # Reindexing a product-box time integral (S3b LADDER-DECAY)

For a finite coordinate set `A` with two injective families of coordinates `ev, eu : Fin n → A`
(with disjoint ranges), the integral over a product box of a function of the coordinates
`(x (ev k), x (eu k))_k` is the integral over the product of the paired boxes, times the volume of
the remaining coordinates. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open MeasureTheory Set Finset

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

/-- The index equivalence `A ≃ (Fin n ⊕ Fin n) ⊕ R`. -/
noncomputable def timeIdx (ev eu : Fin n → A) (hinj : Function.Injective (Sum.elim ev eu)) :
    ((Fin n ⊕ Fin n) ⊕ {a : A // a ∉ Set.range (Sum.elim ev eu)}) ≃ A :=
  (Equiv.sumCongr (Equiv.ofInjective _ hinj) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun a : A => a ∈ Set.range (Sum.elim ev eu)))

lemma timeIdx_inl_inl (ev eu : Fin n → A) (hinj : Function.Injective (Sum.elim ev eu)) (k : Fin n) :
    timeIdx ev eu hinj (Sum.inl (Sum.inl k)) = ev k := rfl

lemma timeIdx_inl_inr (ev eu : Fin n → A) (hinj : Function.Injective (Sum.elim ev eu)) (k : Fin n) :
    timeIdx ev eu hinj (Sum.inl (Sum.inr k)) = eu k := rfl

lemma timeIdx_inr (ev eu : Fin n → A) (hinj : Function.Injective (Sum.elim ev eu))
    (r : {a : A // a ∉ Set.range (Sum.elim ev eu)}) : timeIdx ev eu hinj (Sum.inr r) = r.1 := rfl

/-- The measure-preserving chart of the time coordinates. -/
noncomputable def timeChart (ev eu : Fin n → A) (hinj : Function.Injective (Sum.elim ev eu)) :
    (A → ℝ) ≃ᵐ ((Fin n → ℝ × ℝ) × ({a : A // a ∉ Set.range (Sum.elim ev eu)} → ℝ)) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : A => ℝ) (timeIdx ev eu hinj)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ))).trans
    (MeasurableEquiv.prodCongr
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => ℝ)).trans
        (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm)
      (MeasurableEquiv.refl _))

lemma timeChart_apply (ev eu : Fin n → A) (hinj : Function.Injective (Sum.elim ev eu)) (x : A → ℝ) :
    timeChart ev eu hinj x = ((fun k => (x (ev k), x (eu k))), fun r => x r.1) := by
  refine Prod.ext ?_ ?_
  · funext k
    rfl
  · funext r
    rfl

lemma timeChart_measurePreserving (ev eu : Fin n → A) (hinj : Function.Injective (Sum.elim ev eu)) :
    MeasurePreserving (timeChart ev eu hinj) volume volume := by
  have h1 := (volume_measurePreserving_piCongrLeft (fun _ : A => ℝ) (timeIdx ev eu hinj)).symm
  have h2 := volume_measurePreserving_sumPiEquivProdPi
    (fun _ : (Fin n ⊕ Fin n) ⊕ {a : A // a ∉ Set.range (Sum.elim ev eu)} => ℝ)
  have h3 := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => ℝ)
  have h4 := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm
  have h5 : MeasurePreserving (MeasurableEquiv.refl ({a : A // a ∉ Set.range (Sum.elim ev eu)} → ℝ))
      volume volume := MeasurePreserving.id _
  have h6 := h4.comp h3
  exact ((h6.prod h5).comp h2).comp h1

/-- **Reindexing of a product-box integral.** -/
theorem integral_time_reindex (ev eu : Fin n → A) (hinj : Function.Injective (Sum.elim ev eu))
    (J : A → Set ℝ) (hJ : ∀ a, MeasurableSet (J a)) (G : (Fin n → ℝ × ℝ) → ℝ) :
    ∫ x in Set.pi univ J, G (fun k => (x (ev k), x (eu k))) =
      (∏ r : {a : A // a ∉ Set.range (Sum.elim ev eu)}, (volume (J r.1)).toReal) *
        ∫ y in Set.pi univ (fun k => J (ev k) ×ˢ J (eu k)), G y := by
  set R := {a : A // a ∉ Set.range (Sum.elim ev eu)} with hR
  set B : Set (Fin n → ℝ × ℝ) := Set.pi univ (fun k => J (ev k) ×ˢ J (eu k)) with hB
  set BR : Set (R → ℝ) := Set.pi univ (fun r : R => J r.1) with hBR
  have hmem : ∀ x : A → ℝ, x ∈ Set.pi univ J ↔
      (fun k => (x (ev k), x (eu k))) ∈ B ∧ (fun r : R => x r.1) ∈ BR := by
    intro x
    simp only [Set.mem_pi, Set.mem_univ, true_implies, hB, hBR, Set.mem_prod]
    constructor
    · intro h
      exact ⟨fun k => ⟨h _, h _⟩, fun r => h _⟩
    · rintro ⟨h1, h2⟩ a
      by_cases ha : a ∈ Set.range (Sum.elim ev eu)
      · obtain ⟨j, rfl⟩ := ha
        rcases j with k | k
        · exact (h1 k).1
        · exact (h1 k).2
      · exact h2 ⟨a, ha⟩
  have hBm : MeasurableSet B := MeasurableSet.univ_pi (fun k => (hJ _).prod (hJ _))
  have hBRm : MeasurableSet BR := MeasurableSet.univ_pi (fun r => hJ _)
  have e1 : ∫ x in Set.pi univ J, G (fun k => (x (ev k), x (eu k))) =
      ∫ x, (B.indicator G (timeChart ev eu hinj x).1) * (BR.indicator (fun _ => (1 : ℝ))
        (timeChart ev eu hinj x).2) := by
    rw [← integral_indicator (MeasurableSet.univ_pi hJ)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    dsimp only
    rw [timeChart_apply]
    by_cases hx : x ∈ Set.pi univ J
    · obtain ⟨h1, h2⟩ := (hmem x).mp hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem h1, Set.indicator_of_mem h2]; simp
    · have : ¬ ((fun k => (x (ev k), x (eu k))) ∈ B ∧ (fun r : R => x r.1) ∈ BR) := fun h => hx ((hmem x).mpr h)
      rw [Set.indicator_of_notMem hx]
      by_cases h1 : (fun k => (x (ev k), x (eu k))) ∈ B
      · have h2 : (fun r : R => x r.1) ∉ BR := fun h2 => this ⟨h1, h2⟩
        rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2]; simp
      · rw [Set.indicator_of_notMem h1]; simp
  rw [e1]
  have e2 := (timeChart_measurePreserving ev eu hinj).integral_comp' (g := fun p : (Fin n → ℝ × ℝ) × (R → ℝ) =>
    (B.indicator G p.1) * (BR.indicator (fun _ => (1 : ℝ)) p.2))
  rw [e2, Measure.volume_eq_prod, integral_prod_mul]
  rw [integral_indicator hBm, integral_indicator hBRm]
  simp only [integral_const, smul_eq_mul, mul_one, Measure.restrict_apply_univ]
  rw [mul_comm]
  congr 1
  simp only [Measure.real, hBR]
  rw [Measure.restrict_apply_univ, volume_pi, Measure.pi_pi, ENNReal.toReal_prod]

end WaveTurbulence.LadderDecay
