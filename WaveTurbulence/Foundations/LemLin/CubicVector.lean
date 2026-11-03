/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.CubicEstimate
public import WaveTurbulence.Foundations.LemLin.Transpose

/-!
# TARGET `lemcubic0` in three-vector notation

Inner block coordinates `0,1,2` mean `x,y,z` (or `g,h,q` for the integer
frequency vectors). The definition below is the source integral over three
vectors with standard product Lebesgue measure and the explicit two choices
of Λ. The final theorem includes absolute summability.
-/

public section

namespace WaveTurbulence.LemLin
open MeasureTheory Finset
open scoped Classical

/-- The two vector bilinear forms Λ in the source. -/
@[expose] def vectorLambda {d : ℕ} (kind : CubicPhase) (x y z : Fin d → ℝ) : ℝ :=
  match kind with
  | .cross => dotProduct x z
  | .collision => dotProduct z (x + y - z)

/-- The source quadratic phase, with its explicit scalar parameters. -/
@[expose] def vectorQuadratic {d : ℕ} (kind : CubicPhase) (s t : ℝ)
    (p : Fin 3 → Fin d → ℝ) : ℝ :=
  t * dotProduct (p 0) (p 1) + s * vectorLambda kind (p 0) (p 1) (p 2)

/-- The quadratic phase is the sum of the scalar coordinate phases. -/
theorem vectorQuadratic_eq_sum {d : ℕ} (kind : CubicPhase) (s t : ℝ)
    (p : Fin 3 → Fin d → ℝ) :
    vectorQuadratic kind s t p = ∑ i, scalarQuadratic kind s t (fun j => p j i) := by
  cases kind <;> simp only [vectorQuadratic, vectorLambda, scalarQuadratic,
    dotProduct, Pi.add_apply, Pi.sub_apply, mul_sum, sum_add_distrib, mul_assoc]

/-- TARGET L1546: the actual integral with three vector cutoffs and the two source phases. -/
@[expose] noncomputable def cubicVectorIntegral {d : ℕ} (kind : CubicPhase) (s t : ℝ)
    (a ν : Fin 3 → Fin d → ℝ) : ℂ :=
  ∫ p : Fin 3 → Fin d → ℝ,
    (∏ j, Fourier.chi0TensorComplex (p j - a j)) *
      (Real.fourierChar ((∑ j, dotProduct (ν j) (p j)) + vectorQuadratic kind s t p) : ℂ)

/-- Vector-first and spatial-coordinate-first integrals are exactly equal. -/
theorem cubicVectorIntegral_eq_tensor {d : ℕ} (kind : CubicPhase) (s t : ℝ)
    (a ν : Fin 3 → Fin d → ℝ) :
    cubicVectorIntegral kind s t a ν = cubicTensorIntegral kind s t
      (fun i j => a j i) (fun i j => ν j i) := by
  unfold cubicVectorIntegral cubicTensorIntegral
  rw [← (transposeCoordinates_measurePreserving d 3).integral_comp']
  apply integral_congr_ae
  apply ae_of_all
  intro p
  dsimp only
  have hp : transposeCoordinates d 3 p = fun j i => p i j := rfl
  rw [hp, vectorQuadratic_eq_sum]
  have he : (∑ j, dotProduct (ν j) (fun i => p i j)) +
      (∑ i, scalarQuadratic kind s t (fun j => p i j)) =
      ∑ i, ((∑ j, ν j i * p i j) + scalarQuadratic kind s t (p i)) := by
    simp only [dotProduct, sum_add_distrib]
    rw [sum_comm]
  have hc : (∏ j, Fourier.chi0TensorComplex ((fun i => p i j) - a j)) =
      ∏ j, Fourier.chi0TensorComplex (fun i => p i j - a j i) := rfl
  rw [he, hc]

/-- The three source integer frequency vectors `Lg+ξ`, `Lh+ξ'`, `Lq+ξ''`. -/
@[expose] def vectorLatticeFrequency {d : ℕ} (L : ℝ) (ξ : Fin 3 → Fin d → ℝ)
    (n : Fin 3 → Fin d → ℤ) : Fin 3 → Fin d → ℝ := fun j i => L * n j i + ξ j i

/-- TARGET `lemcubic0`, with the paper's three-vector integral and frequency indexing. -/
theorem lemcubic0_vector (d : ℕ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ {L : ℝ}, 1 ≤ L → ∀ (kind : CubicPhase) (s t : ℝ), |s| ≤ L → |t| ≤ L →
      ∀ (a ξ : Fin 3 → Fin d → ℝ),
      Summable (fun n : Fin 3 → Fin d → ℤ =>
        ‖cubicVectorIntegral kind s t a (vectorLatticeFrequency L ξ n)‖) ∧
      (∑' n : Fin 3 → Fin d → ℤ,
        ‖cubicVectorIntegral kind s t a (vectorLatticeFrequency L ξ n)‖) ≤
          K / (1 + |s| + |t|) ^ d := by
  obtain ⟨K, hK, hbound⟩ := lemcubic0 d
  refine ⟨K, hK, ?_⟩
  intro L hL kind s t hs ht a ξ
  let e : (Fin d → Fin 3 → ℤ) ≃ (Fin 3 → Fin d → ℤ) := Equiv.piComm (fun _ _ => ℤ)
  let F : (Fin 3 → Fin d → ℤ) → ℝ := fun n =>
    ‖cubicVectorIntegral kind s t a (vectorLatticeFrequency L ξ n)‖
  have he (n : Fin d → Fin 3 → ℤ) : F (e n) =
      ‖cubicTensorIntegral kind s t (fun i j => a j i)
        (tensorLatticeFrequency L (fun i j => ξ j i) n)‖ := by
    dsimp only [F]
    rw [cubicVectorIntegral_eq_tensor]
    rfl
  have hb := hbound hL kind s t hs ht (fun i j => a j i) (fun i j => ξ j i)
  have hS : Summable (F ∘ e) := by simpa only [Function.comp_def, he] using hb.1
  refine ⟨e.summable_iff.mp hS, ?_⟩
  calc
    _ = ∑' n : Fin d → Fin 3 → ℤ, F (e n) := (e.tsum_eq F).symm
    _ ≤ _ := by simpa only [he] using hb.2

end WaveTurbulence.LemLin
