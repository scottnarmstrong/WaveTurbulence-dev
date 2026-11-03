/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.JointFourierFactors
public import WaveTurbulence.Foundations.WeylSums.FiniteParityBlocks
public import WaveTurbulence.Foundations.WeylSums.WeylSymmetry

/-! # Joint Fourier reduction with sum/difference parity constraints -/

public section
open Finset MeasureTheory
open scoped BigOperators
namespace WaveTurbulence.WeylSums

/-- Insert one two-coordinate block into the joint Euclidean space. -/
@[expose] noncomputable def pairBlockVector {d : ℕ} (j : Fin d) (p q : ℝ) :
    EuclideanSpace ℝ (Fin d × Fin 2) :=
  EuclideanSpace.single (j,0) p + EuclideanSpace.single (j,1) q

theorem inner_pairBlockVector {d : ℕ} (ξ : EuclideanSpace ℝ (Fin d × Fin 2))
    (j : Fin d) (p q : ℝ) :
    inner ℝ ξ (pairBlockVector j p q) = p*ξ (j,0)+q*ξ (j,1) := by
  simp [pairBlockVector, inner_add_right, EuclideanSpace.inner_single_right]

/-- A finite parity-restricted Fourier superposition is bounded by `G(u)²`
per coordinate. No factor depending on a parity class is lost. -/
theorem norm_parity_fourier_reduction_le {d : ℕ} {M L : ℝ} (hM : 0 < M)
    (F : EuclideanSpace ℝ (Fin d × Fin 2) → ℂ) (hF : Integrable F)
    (h : Fin d × Fin 2 → ℤ) (u r w : Fin d → ℝ) :
    ‖∑ v : Fin d → (↥(Icc (-⌈M⌉ : ℤ) ⌈M⌉) × ↥(Icc (-⌈M⌉ : ℤ) ⌈M⌉)),
      (∏ j, if Even (((v j).1 : ℤ)+h (j,0)-((v j).2 : ℤ)-h (j,1)) then
        weylCutoff (((v j).1 : ℤ)/M)*weylCutoff (((v j).2 : ℤ)/M) else 0) *
      (∫ ξ, F ξ*e (inner ℝ ξ (∑ j, pairBlockVector j
        (((((v j).1 : ℤ) : ℝ)+h (j,0))/L)
        (((((v j).2 : ℤ) : ℝ)+h (j,1))/L)))) *
      e (∑ j, (u j*((((v j).1 : ℤ) : ℝ)+h (j,0))^2-
        u j*((((v j).2 : ℤ) : ℝ)+h (j,1))^2+
        r j*((((v j).1 : ℤ) : ℝ)+h (j,0))+
        w j*((((v j).2 : ℤ) : ℝ)+h (j,1))))‖ ≤
      (∫ ξ, ‖F ξ‖) * ∏ j, weylSupremum M (u j)^2 := by
  classical
  let K := ↥(Icc (-⌈M⌉ : ℤ) ⌈M⌉)
  let p (j : Fin d) (n : K) : ℤ := n.val+h (j,0)
  let q (j : Fin d) (n : K) : ℤ := n.val+h (j,1)
  let θ (j : Fin d) (ab : K × K) : ℂ :=
    if Even (p j ab.1-q j ab.2) then weylCutoff ((ab.1 : ℤ)/M)*weylCutoff ((ab.2 : ℤ)/M) else 0
  let X (j : Fin d) (ab : K × K) := pairBlockVector j ((p j ab.1 : ℝ)/L) ((q j ab.2 : ℝ)/L)
  let φ (j : Fin d) (ab : K × K) := u j*(p j ab.1 : ℝ)^2-u j*(q j ab.2 : ℝ)^2+
    r j*p j ab.1+w j*q j ab.2
  have hb (ξ : EuclideanSpace ℝ (Fin d × Fin 2)) (j : Fin d) :
      ‖∑ ab : K × K, θ j ab*e (φ j ab+inner ℝ ξ (X j ab))‖ ≤ weylSupremum M (u j)^2 := by
    have hsingle (s ρ : ℝ) (center : ℤ) :
        ‖∑ n : K, weylCutoff ((n : ℤ)/M)*e (s*((n : ℝ)+center)^2+ρ*((n : ℝ)+center))‖ ≤
          weylSupremum M s := by
      rw [sum_coe_sort (Icc (-⌈M⌉ : ℤ) ⌈M⌉)
        (fun n => weylCutoff ((n : ℝ)/M)*e (s*((n : ℝ)+center)^2+ρ*((n : ℝ)+center)))]
      exact norm_shifted_weyl_factor_le hM s ρ center
    have hh := norm_finite_parity_pair_le
      (fun n : K => weylCutoff ((n : ℤ)/M)) (fun n : K => weylCutoff ((n : ℤ)/M))
      (p j) (q j) (u j) (-u j) (r j+ξ (j,0)/L) (w j+ξ (j,1)/L)
      (weylSupremum M (u j)) (weylSupremum M (-u j))
      (fun ρ => by simpa only [p, Int.cast_add] using hsingle (u j) ρ (h (j,0)))
      (fun ρ => by simpa only [q, Int.cast_add] using hsingle (-u j) ρ (h (j,1)))
    rw [weylSupremum_neg hM] at hh
    rw [← pow_two] at hh
    convert hh using 1
    congr 1
    apply sum_congr rfl
    intro ab hab
    congr 2
    dsimp [φ, X]
    rw [inner_pairBlockVector]
    ring
  have hh := norm_joint_fourier_factorization_le F hF θ X φ
    (fun j => weylSupremum M (u j)^2) hb
  convert hh using 1
  congr 1
  apply sum_congr rfl
  intro v hv
  simp only [θ, X, φ, p, q, Int.cast_add, sub_sub]

end WaveTurbulence.WeylSums
