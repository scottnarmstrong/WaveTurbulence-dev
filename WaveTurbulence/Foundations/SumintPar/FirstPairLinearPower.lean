/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.BadBlockPowerMargins
public import WaveTurbulence.Foundations.SumintPar.StrictPowerAbsorption

/-!
# The first bad pair uses different linear estimates on its two contributions

This numerical comparison retains the stationary and Weyl terms separately.
It accepts bounds on a scalar J and is not a source theorem. Its source use
is the distinguished-time integral after insertion of the uniform first-pair
mass bound. Coefficients may depend on delta and Dsteps: only the later
threshold depends on them. The same threshold works for every block.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.SumintPar

/-- A scalar satisfying two linear bounds can use one on each nonnegative pair contribution. -/
theorem first_pair_linear_split {J X Y S W : ℝ} (hX : J ≤ X) (hY : J ≤ Y)
    (hS : 0 ≤ S) (hW : 0 ≤ W) : J*(S+W) ≤ X*S+Y*W := by
  rw [mul_add]
  exact add_le_add (mul_le_mul_of_nonneg_right hX hS) (mul_le_mul_of_nonneg_right hY hW)

/-- Both case-(a) and case-(c) first-pair stationary powers leave a strict basic reserve. -/
theorem first_pair_stationary_exponent {γ p : ℝ} (hγ : γ ∈ Set.Ioo (0:ℝ) 1)
    (hp : 7/8 ≤ p) : gammaBase γ/2 < 2*γ*p-γ := by
  have hb : gammaBase γ ≤ γ := min_le_left _ _
  have hm := mul_nonneg hγ.1.le (sub_nonneg.mpr hp)
  nlinarith only [hγ.1,hb,hm]

/-- Conditional numerical comparison used to pair the actual first-pair envelope with its linear mass. -/
theorem exists_first_pair_linear_power_bound (d : ℕ) (hd : 3 ≤ d) {γ η p : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη : η ≤ gammaBase γ) (hp : 7/8 ≤ p)
    (K₀ K₁ Ks Kw : ℝ) (hKs : 0 ≤ Ks) (hKw : 0 ≤ Kw) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R, ∀ J : ℝ,
      J ≤ K₀*L^(d:ℝ) → J ≤ K₁*L^((d:ℝ)-γ+gammaBase γ) →
      J*(Ks*L^(2*(d:ℝ)-2*γ*(1+p))+
        Kw*L^(2*(d:ℝ)-2*γ-2*((d:ℝ)-1)*(1-γ)+η)) ≤
      L^(3*((d:ℝ)-γ)-gammaBase γ/2) := by
  have hs := first_pair_stationary_exponent hγ hp
  have hw := bad_pair_weyl_reserve hd hγ
  have hb := gammaBase_pos hγ
  have heS : 3*(d:ℝ)-2*γ*(1+p) < 3*((d:ℝ)-γ)-gammaBase γ/2 := by linarith only [hs]
  have heW : 3*(d:ℝ)-3*γ+gammaBase γ-2*((d:ℝ)-1)*(1-γ)+η <
      3*((d:ℝ)-γ)-gammaBase γ/2 := by linarith only [hw,hη,hb]
  obtain ⟨R,hR,hbound⟩ := exists_three_plain_power_sum_le (K₀*Ks) (K₁*Kw) 0
    (3*(d:ℝ)-2*γ*(1+p)) (3*(d:ℝ)-3*γ+gammaBase γ-2*((d:ℝ)-1)*(1-γ)+η)
    (3*(d:ℝ)-2*γ*(1+p)) (3*((d:ℝ)-γ)-gammaBase γ/2) heS heW heS
  refine ⟨R,hR,?_⟩
  intro L hL J hJ₀ hJ₁
  have hLp : 0 < L := by linarith [hR.trans hL]
  have hpS : L^(d:ℝ)*L^(2*(d:ℝ)-2*γ*(1+p)) = L^(3*(d:ℝ)-2*γ*(1+p)) := by
    rw [← Real.rpow_add hLp]; congr 1; ring
  have hpW : L^((d:ℝ)-γ+gammaBase γ)*L^(2*(d:ℝ)-2*γ-2*((d:ℝ)-1)*(1-γ)+η) =
      L^(3*(d:ℝ)-3*γ+gammaBase γ-2*((d:ℝ)-1)*(1-γ)+η) := by
    rw [← Real.rpow_add hLp]; congr 1; ring
  calc
    _ ≤ (K₀*L^(d:ℝ))*(Ks*L^(2*(d:ℝ)-2*γ*(1+p)))+
        (K₁*L^((d:ℝ)-γ+gammaBase γ))*(Kw*L^(2*(d:ℝ)-2*γ-2*((d:ℝ)-1)*(1-γ)+η)) :=
      first_pair_linear_split hJ₀ hJ₁ (by positivity) (by positivity)
    _ = (K₀*Ks)*L^(3*(d:ℝ)-2*γ*(1+p))+
        (K₁*Kw)*L^(3*(d:ℝ)-3*γ+gammaBase γ-2*((d:ℝ)-1)*(1-γ)+η) := by
      calc
        _ = (K₀*Ks)*(L^(d:ℝ)*L^(2*(d:ℝ)-2*γ*(1+p)))+
          (K₁*Kw)*(L^((d:ℝ)-γ+gammaBase γ)*L^(2*(d:ℝ)-2*γ-2*((d:ℝ)-1)*(1-γ)+η)) := by ring
        _ = _ := by rw [hpS,hpW]
    _ ≤ _ := by simpa only [zero_mul,add_zero] using hbound L hL

end WaveTurbulence.SumintPar
