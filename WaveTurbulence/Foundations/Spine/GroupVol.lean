/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Valley
import Mathlib.Tactic
/-! Volume of a product of valley regions on disjoint coordinate groups. -/
@[expose] public section
open MeasureTheory Set Finset Function
open scoped ENNReal
namespace WaveTurbulence.Ladder

section Curry
variable {Q : Type} [Fintype Q] [DecidableEq Q] {K : Q → Type} [∀ q, Fintype (K q)] [∀ q, DecidableEq (K q)]

theorem measurePreserving_piCurry_volume :
    MeasurePreserving (MeasurableEquiv.piCurry (fun (q : Q) (_ : K q) => ℝ))
      (volume : Measure ((Σ q, K q) → ℝ)) (Measure.pi fun q => (volume : Measure (K q → ℝ))) := by
  set X : (q : Q) → K q → Type := fun _ _ => ℝ
  set ν : Measure ((q : Q) → (K q → ℝ)) := Measure.pi fun q => (volume : Measure (K q → ℝ)) with hν
  have hmeas : Measurable (MeasurableEquiv.piCurry X) := (MeasurableEquiv.piCurry X).measurable
  have h : (volume : Measure ((Σ q, K q) → ℝ)) = Measure.map (MeasurableEquiv.piCurry X).symm ν := by
    rw [volume_pi]
    apply Measure.pi_eq
    intro s hs
    rw [Measure.map_apply (MeasurableEquiv.piCurry X).symm.measurable (MeasurableSet.univ_pi hs)]
    have : (MeasurableEquiv.piCurry X).symm ⁻¹' Set.pi univ s =
        Set.pi univ (fun q => Set.pi univ (fun i : K q => s ⟨q, i⟩)) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, MeasurableEquiv.coe_piCurry_symm]
      constructor
      · intro h q i; exact h ⟨q, i⟩
      · rintro h ⟨q, i⟩; exact h q i
    rw [this, hν, Measure.pi_pi]
    simp only [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_sigma]
  refine ⟨hmeas, ?_⟩
  rw [h, Measure.map_map hmeas (MeasurableEquiv.piCurry X).symm.measurable]
  simp

end Curry

theorem volume_groups {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q] (K : Q → ℕ)
    (σ : Fin k ≃ Σ q, Fin (K q)) {D : ℝ} (hD : 0 ≤ D) :
    volume {x : Fin k → ℝ | ∀ q, (fun j : Fin (K q) => x (σ.symm ⟨q, j⟩)) ∈ Vset (K q) D} ≤
      ∏ q, ENNReal.ofReal (2 ^ (K q) * D ^ (K q) / (Nat.factorial (K q) : ℝ)) := by
  have h1 := volume_measurePreserving_piCongrLeft (fun _ : (Σ q, Fin (K q)) => ℝ) σ
  have h2 := (measurePreserving_piCurry_volume (Q := Q) (K := fun q => Fin (K q))).comp h1
  have hset : {x : Fin k → ℝ | ∀ q, (fun j : Fin (K q) => x (σ.symm ⟨q, j⟩)) ∈ Vset (K q) D} =
      ((MeasurableEquiv.piCurry (fun (q : Q) (_ : Fin (K q)) => ℝ)) ∘
        (MeasurableEquiv.piCongrLeft (fun _ : (Σ q, Fin (K q)) => ℝ) σ)) ⁻¹'
        (Set.pi univ (fun q => Vset (K q) D)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Function.comp_apply, Set.mem_pi, Set.mem_univ,
      true_implies]
    refine forall_congr' (fun q => ?_)
    have : (MeasurableEquiv.piCurry (fun (q : Q) (_ : Fin (K q)) => ℝ))
        ((MeasurableEquiv.piCongrLeft (fun _ : (Σ q, Fin (K q)) => ℝ) σ) x) q =
        fun j : Fin (K q) => x (σ.symm ⟨q, j⟩) := by
      funext j
      rw [MeasurableEquiv.coe_piCurry]
      simp only [Sigma.curry]
      have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : (Σ q, Fin (K q)) => ℝ) σ x (σ.symm ⟨q, j⟩)
      simpa using this
    rw [this]
  rw [hset, h2.measure_preimage (MeasurableSet.univ_pi (fun q => measurableSet_Vset _ _)).nullMeasurableSet,
    Measure.pi_pi]
  exact Finset.prod_le_prod' (fun q _ => volume_Vset_le (K q) hD)

end WaveTurbulence.Ladder
