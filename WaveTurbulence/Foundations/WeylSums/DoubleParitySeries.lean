/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.ParitySeries

/-! # Two parity projectors in the cubic change of variables -/

public section
namespace WaveTurbulence.WeylSums

/-- The finite-amplitude character identity on an arbitrary discrete carrier. -/
theorem tsum_finite_parity_eq {α : Type*} (A : α → ℂ)
    (hA : (Function.support A).Finite) (k : α → ℤ) (φ : α → ℝ) :
    (∑' v, (if Even (k v) then A v else 0)*e (φ v)) =
      ((∑' v, A v*e (φ v))+(∑' v, A v*e (φ v+(k v : ℝ)/2)))/2 := by
  classical
  have heq (v : α) : (if Even (k v) then A v else 0)*e (φ v) =
      (A v*e (φ v)+A v*e (φ v+(k v : ℝ)/2))/2 := by
    calc
      _ = A v*((if Even (k v) then (1 : ℂ) else 0)*e (φ v)) := by
        by_cases h : Even (k v) <;> simp [h]
      _ = A v*((e (φ v)+e (φ v+(k v : ℝ)/2))/2) := by rw [parity_phase]
      _ = _ := by ring
  simp_rw [heq]
  rw [tsum_div_const, (summable_finite_amplitude A hA φ).tsum_add
    (summable_finite_amplitude A hA (fun v => φ v+(k v : ℝ)/2))]

/-- A parity projector preserves a bound that is uniform in its two
character shifts. -/
theorem norm_tsum_finite_parity_le {α : Type*} (A : α → ℂ)
    (hA : (Function.support A).Finite) (k : α → ℤ) (φ : α → ℝ) (B : ℝ)
    (h₀ : ‖∑' v, A v*e (φ v)‖ ≤ B)
    (h₁ : ‖∑' v, A v*e (φ v+(k v : ℝ)/2)‖ ≤ B) :
    ‖∑' v, (if Even (k v) then A v else 0)*e (φ v)‖ ≤ B := by
  rw [tsum_finite_parity_eq A hA k φ, norm_div]
  norm_num only [Complex.norm_ofNat]
  exact (div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)).trans (by linarith)

/-- Two simultaneous parity constraints preserve a bound uniform in all
linear combinations of the corresponding characters. -/
theorem norm_tsum_double_parity_le {α : Type*} (A : α → ℂ)
    (hA : (Function.support A).Finite) (k l : α → ℤ) (φ : α → ℝ) (B : ℝ)
    (hb : ∀ r t : ℝ, ‖∑' v, A v*e (φ v+r*(k v : ℝ)/2+t*(l v : ℝ)/2)‖ ≤ B) :
    ‖∑' v, (if Even (k v) ∧ Even (l v) then A v else 0)*e (φ v)‖ ≤ B := by
  classical
  let A₁ : α → ℂ := fun v => if Even (k v) then A v else 0
  have hA₁ : (Function.support A₁).Finite := by
    apply hA.subset
    intro v hv
    by_contra hz
    have hz' : A v = 0 := Function.notMem_support.mp hz
    exact hv (by simp [A₁,hz'])
  have hsingle (t : ℝ) : ‖∑' v, A₁ v*e (φ v+t*(l v : ℝ)/2)‖ ≤ B := by
    apply norm_tsum_finite_parity_le A hA k (fun v => φ v+t*(l v : ℝ)/2) B
    · simpa only [zero_mul,zero_div,add_zero] using hb 0 t
    · convert hb 1 t using 1
      congr 1
      apply tsum_congr
      intro v
      congr 2
      ring
  have hh := norm_tsum_finite_parity_le A₁ hA₁ l φ B
    (by simpa only [zero_mul,zero_div,add_zero] using hsingle 0)
    (by simpa only [one_mul] using hsingle 1)
  convert hh using 1
  congr 1
  apply tsum_congr
  intro v
  by_cases hk : Even (k v) <;> by_cases hl : Even (l v) <;> simp [A₁,hk,hl]

end WaveTurbulence.WeylSums
