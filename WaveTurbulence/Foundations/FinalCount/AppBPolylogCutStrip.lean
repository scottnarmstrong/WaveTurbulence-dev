/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCutPairDifference
import Mathlib.Tactic

/-! # Two-bond cut strips with a polylogarithmic component energy window -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_atomic_window_le_width {L δ γ : ℝ} (hL : 1 ≤ L) (hδ : 0 ≤ δ) (m : ℕ) :
    δ⁻¹*L^(-2*γ) ≤ appbWidth δ γ m L := by
  have hp : (1 : ℝ) ≤ (1+Real.log L)^m := one_le_pow₀ (by linarith [Real.log_nonneg hL])
  have hn : 0 ≤ δ⁻¹*L^(-2*γ) := mul_nonneg (inv_nonneg.mpr hδ) (Real.rpow_nonneg (zero_le_one.trans hL) _)
  have hh := mul_le_mul_of_nonneg_right hp hn
  simpa only [appbWidth,one_mul,mul_left_comm,mul_assoc] using hh

namespace AppbCutPair
variable {M : Molecule V D} {P : AppbPattern} {r : AppbRealization M P} {S : Finset V}
    (p : AppbCutPair r S)

theorem strip_bound_polylog
    (hopp : appbCutSign M S (r.edge p.first).val ≠ appbCutSign M S (r.edge p.second).val)
    {d : ℕ} {L : ℝ} (hL : 1 ≤ L) (γ δ : ℝ) (hδ : 0 < δ) (m : ℕ)
    (hcard : (S.card : ℝ) ≤ 2*(1+Real.log L)^m)
    (w : Mom d) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hres : M.IsRestricted L γ δ w β k0 κ) :
    let R := (((appbCutSign M S (r.edge p.first).val)⁻¹ : ℤˣ) : ℤ) • (∑ v ∈ S,c v)
    |inner ℝ R (Molecule.kvec L w (r.localLabels κ) p.first)-
      ((((appbCutSign M S (r.edge p.first).val)⁻¹ : ℤˣ) : ℤ)*(∑ v ∈ S,β v)+‖R‖^2)/2| ≤ appbWidth δ γ m L := by
  have hLp := zero_lt_one.trans_le hL
  have hτ : 0 ≤ δ⁻¹*L^(-2*γ) := by positivity
  have he := p.energy_difference hopp L γ δ w c β k0 κ hκ hres
  have hwin : (S.card : ℝ)*(δ⁻¹*L^(-2*γ)) ≤ 2*appbWidth δ γ m L := by
    exact (mul_le_mul_of_nonneg_right hcard hτ).trans_eq (by unfold appbWidth; ring)
  exact appb_difference_strip_bound _ _ _ _ _ (p.momentum_difference hopp L w c κ hκ).symm (he.trans hwin)

end AppbCutPair
end WaveTurbulence.Mole
