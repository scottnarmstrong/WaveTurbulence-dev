/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
# Product-measure regrouping for the source time factors

Finite-product nonnegative Fubini and dependent currying of coordinates
are reused from Scott's Balaban development. Both proofs are reproduced
here and checked against this project's pinned Mathlib.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.SumintPar

open MeasureTheory ENNReal

universe u v

/-- The `ℝ≥0∞` version of Fubini for a product of functions of independent coordinates. -/
theorem lintegral_fintype_prod_eq_prod (ι : Type u) [Fintype ι] : ∀ {E : ι → Type v}
    [∀ i, MeasurableSpace (E i)] {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → E i → ℝ≥0∞) (_ : ∀ i, Measurable (f i)),
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ {E : ι → Type v}
      [∀ i, MeasurableSpace (E i)] {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
      (f : (i : ι) → E i → ℝ≥0∞) (_ : ∀ i, Measurable (f i)),
      ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i)) ?_ ?_ ?_ ι
  · intro α β _ e ih E mE μ _ f hf
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (E := fun a => E (e a)) (μ := fun a => μ (e a)) (fun a => f (e a))
      (fun a => hf _)
    rw [← (measurePreserving_piCongrLeft μ e).lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _)]
    simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    rw [h]
  · intro E mE μ _ f _
    simp
  · intro α _ ih E mE μ _ f hf
    rw [← Measure.pi_map_piOptionEquivProd μ]
    rw [lintegral_map_equiv _ (MeasurableEquiv.piOptionEquivProd E).symm]
    have key : ∀ a : ((i : α) → E (some i)) × E none,
        ∏ i, f i ((MeasurableEquiv.piOptionEquivProd E).symm a i) =
          (∏ i : α, f (some i) (a.1 i)) * f none a.2 := by
      intro a
      rw [Fintype.prod_option]
      have h1 : (MeasurableEquiv.piOptionEquivProd E).symm a none = a.2 := rfl
      have h2 : ∀ i, (MeasurableEquiv.piOptionEquivProd E).symm a (some i) = a.1 i := fun i => rfl
      rw [h1]; simp_rw [h2]; ring
    simp_rw [key]
    rw [lintegral_prod_mul (f := fun y : (i : α) → E (some i) => ∏ i : α, f (some i) (y i))
      (g := f none) (μ := Measure.pi fun i => μ (some i)) (ν := μ none)
      (Finset.measurable_prod _ fun i _ => (hf (some i)).comp (measurable_pi_apply i)).aemeasurable
      (hf none).aemeasurable]
    rw [ih (fun i => f (some i)) (fun i => hf _), Fintype.prod_option]
    ring


theorem measurePreserving_piCurry {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ j, Fintype (κ j)]
    (X : (j : ι) → κ j → Type*) [∀ j k, MeasurableSpace (X j k)]
    (μ : ∀ j k, Measure (X j k)) [∀ j k, SigmaFinite (μ j k)] :
    MeasurePreserving (MeasurableEquiv.piCurry X)
      (Measure.pi fun a : (Σ j, κ j) => μ a.1 a.2)
      (Measure.pi fun j => Measure.pi fun k => μ j k) := by
  set e := MeasurableEquiv.piCurry X with he
  have hsymm : MeasurePreserving e.symm (Measure.pi fun j => Measure.pi fun k => μ j k)
      (Measure.pi fun a : (Σ j, κ j) => μ a.1 a.2) := by
    refine ⟨e.symm.measurable, (Measure.pi_eq fun s hs => ?_).symm⟩
    have hpre : e.symm ⁻¹' Set.pi Set.univ s =
        Set.pi Set.univ fun j => Set.pi Set.univ fun k => s ⟨j, k⟩ := by
      ext g
      simp [he, MeasurableEquiv.piCurry]
      exact ⟨fun h i j => h ⟨i, j⟩, fun h ⟨i, j⟩ => h i j⟩
    rw [e.symm.map_apply, hpre, Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    exact (Fintype.prod_sigma (fun a : (Σ j, κ j) => μ a.1 a.2 (s a))).symm
  simpa using MeasurePreserving.symm e.symm hsymm

/-- Currying finite families of real coordinates preserves the actual product Lebesgue measure. -/
theorem volume_measurePreserving_piCurry {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] :
    MeasurePreserving (MeasurableEquiv.piCurry (fun (i : ι) (_ : κ i) => ℝ)) volume volume := by
  simpa only [volume_pi] using
    measurePreserving_piCurry (fun (i : ι) (_ : κ i) => ℝ) (fun _ _ => volume)

end WaveTurbulence.SumintPar
