/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.ParitySeries
public import WaveTurbulence.Foundations.WeylSums.WeylTensorFactors
public import Mathlib.Data.Fintype.Prod

/-! # Parity averaging for finite Fourier blocks -/

public section
open Finset
open scoped BigOperators
namespace WaveTurbulence.WeylSums

/-- The parity projector averages two linear frequency shifts, on any finite index set. -/
theorem sum_finite_parity {κ : Type*} [Fintype κ] (A : κ → ℂ) (k : κ → ℤ)
    (φ : κ → ℝ) :
    (∑ v, (if Even (k v) then A v else 0) * e (φ v)) =
      ((∑ v, A v*e (φ v)) + (∑ v, A v*e (φ v+(k v : ℝ)/2)))/2 := by
  classical
  rw [← sum_add_distrib, sum_div]
  apply sum_congr rfl
  intro v hv
  calc
    _ = A v*((if Even (k v) then (1 : ℂ) else 0)*e (φ v)) := by
      by_cases h : Even (k v) <;> simp [h]
    _ = A v*((e (φ v)+e (φ v+(k v : ℝ)/2))/2) := by rw [parity_phase]
    _ = _ := by ring

/-- A parity-coupled pair of separated finite sums costs only the product
of their frequency-uniform bounds. -/
theorem norm_finite_parity_pair_le {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℂ) (g : β → ℂ) (p : α → ℤ) (q : β → ℤ)
    (u v r w U V : ℝ)
    (hf : ∀ ρ : ℝ, ‖∑ a, f a*e (u*(p a : ℝ)^2+ρ*p a)‖ ≤ U)
    (hg : ∀ ρ : ℝ, ‖∑ b, g b*e (v*(q b : ℝ)^2+ρ*q b)‖ ≤ V) :
    ‖∑ ab : α × β, (if Even (p ab.1-q ab.2) then f ab.1*g ab.2 else 0)*
      e (u*(p ab.1 : ℝ)^2+v*(q ab.2 : ℝ)^2+r*p ab.1+w*q ab.2)‖ ≤ U*V := by
  classical
  let A (ab : α × β) := f ab.1*g ab.2
  let φ (ab : α × β) := u*(p ab.1 : ℝ)^2+v*(q ab.2 : ℝ)^2+r*p ab.1+w*q ab.2
  have hfactor (r w : ℝ) :
      (∑ ab : α × β, A ab*e (u*(p ab.1 : ℝ)^2+v*(q ab.2 : ℝ)^2+r*p ab.1+w*q ab.2)) =
      (∑ a, f a*e (u*(p a : ℝ)^2+r*p a)) *
      (∑ b, g b*e (v*(q b : ℝ)^2+w*q b)) := by
    rw [Fintype.sum_prod_type, sum_mul]
    apply sum_congr rfl
    intro a ha
    rw [mul_sum]
    apply sum_congr rfl
    intro b hb
    have he : u*(p a : ℝ)^2+v*(q b : ℝ)^2+r*p a+w*q b =
        (u*(p a : ℝ)^2+r*p a)+(v*(q b : ℝ)^2+w*q b) := by ring
    rw [he, e_add]
    dsimp [A]
    ring
  have hbound (r w : ℝ) :
      ‖∑ ab : α × β, A ab*e (u*(p ab.1 : ℝ)^2+v*(q ab.2 : ℝ)^2+r*p ab.1+w*q ab.2)‖ ≤ U*V := by
    rw [hfactor, norm_mul]
    exact mul_le_mul (hf r) (hg w) (norm_nonneg _) ((norm_nonneg _).trans (hf r))
  have hshift : (∑ ab : α × β, A ab*e (φ ab+((p ab.1-q ab.2 : ℤ) : ℝ)/2)) =
      ∑ ab : α × β, A ab*e (u*(p ab.1 : ℝ)^2+v*(q ab.2 : ℝ)^2+
        (r+1/2)*p ab.1+(w-1/2)*q ab.2) := by
    apply sum_congr rfl
    intro ab hab
    congr 2
    dsimp [φ]
    push_cast
    ring
  change ‖∑ ab : α × β, (if Even (p ab.1-q ab.2) then A ab else 0)*e (φ ab)‖ ≤ _
  rw [sum_finite_parity, norm_div]
  norm_num only [Complex.norm_ofNat]
  rw [hshift]
  exact (div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)).trans
    (by have h₀ := hbound r w; have h₁ := hbound (r+1/2) (w-1/2); dsimp [φ] at *; linarith)

end WaveTurbulence.WeylSums
