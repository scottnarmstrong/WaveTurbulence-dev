/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Core1
public import WaveTurbulence.Foundations.Spine.BoxSup
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic
/-! Transport from `ι → ℝ` to the product model `(Fin k → ℝ) × (Fin m → ℝ)` and null sets
(hyperplanes `t a = c`, diagonals `t a = t b`). -/
@[expose] public section
open MeasureTheory Set Finset Function
open scoped ENNReal
namespace WaveTurbulence.Ladder
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k m : ℕ}

/-- The measure-preserving coordinate change. -/
noncomputable def Th (e : ι ≃ Fin k ⊕ Fin m) : (ι → ℝ) ≃ᵐ (Fin k → ℝ) × (Fin m → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin k ⊕ Fin m => ℝ) e).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin m => ℝ))

theorem Th_apply (e : ι ≃ Fin k ⊕ Fin m) (t : ι → ℝ) :
    Th e t = (fun i => t (e.symm (Sum.inl i)), fun j => t (e.symm (Sum.inr j))) := by
  have h1 : ∀ s : Fin k ⊕ Fin m, (MeasurableEquiv.piCongrLeft (fun _ : Fin k ⊕ Fin m => ℝ) e t) s =
      t (e.symm s) := by
    intro s
    have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin k ⊕ Fin m => ℝ) e t (e.symm s)
    simpa using this
  ext
  · simp [Th, MeasurableEquiv.coe_sumPiEquivProdPi, h1]
  · simp [Th, MeasurableEquiv.coe_sumPiEquivProdPi, h1]

theorem Th_mp (e : ι ≃ Fin k ⊕ Fin m) : MeasurePreserving (Th e) volume volume :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin k ⊕ Fin m => ℝ)).comp
    (volume_measurePreserving_piCongrLeft (fun _ : Fin k ⊕ Fin m => ℝ) e)

theorem Th_symm_apply (e : ι ≃ Fin k ⊕ Fin m) (p : (Fin k → ℝ) × (Fin m → ℝ)) (v : ι) :
    (Th e).symm p v = Sum.elim p.1 p.2 (e v) := by
  have h : Th e ((Th e).symm p) = p := (Th e).apply_symm_apply p
  rw [Th_apply] at h
  rcases hs : e v with i | j
  · have := congrFun (congrArg Prod.fst h) i
    simp only [Sum.elim_inl]
    rw [← this]; simp [← hs]
  · have := congrFun (congrArg Prod.snd h) j
    simp only [Sum.elim_inr]
    rw [← this]; simp [← hs]

theorem volume_eval_eq (a : ι) (c : ℝ) : volume {t : ι → ℝ | t a = c} = 0 := by
  rw [volume_pi]
  exact Measure.pi_hyperplane (fun _ : ι => (volume : Measure ℝ)) a c

theorem volume_diag_eq {a b : ι} (hab : a ≠ b) : volume {t : ι → ℝ | t a = t b} = 0 := by
  let f : (ι → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj a : (ι → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj b
  have hne : LinearMap.ker f ≠ ⊤ := by
    intro h
    have : Pi.single a (1 : ℝ) ∈ LinearMap.ker f := by rw [h]; trivial
    simp [f, LinearMap.mem_ker, Pi.single_apply, hab.symm] at this
  have := Measure.addHaar_submodule (volume : Measure (ι → ℝ)) (LinearMap.ker f) hne
  convert this using 2
  ext t
  simp [f, LinearMap.mem_ker, sub_eq_zero]

end WaveTurbulence.Ladder
