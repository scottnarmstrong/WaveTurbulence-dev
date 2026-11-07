/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCutPairDifference
public import WaveTurbulence.Foundations.FinalCount.AppBLogWindows
import Mathlib.Tactic

/-! # Energy strips from cuts with polynomial logarithmic size -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbCutPair
variable {M : Molecule V D} {P : AppbPattern} {r : AppbRealization M P} {S : Finset V}
    (p : AppbCutPair r S)

theorem strip_bound_log {d : ℕ} {L : ℝ} (hL : 1 ≤ L) (γ δ : ℝ) (hδ : 0 < δ) (m : ℕ)
    (hopp : appbCutSign M S (r.edge p.first).val ≠ appbCutSign M S (r.edge p.second).val)
    (hcard : (S.card : ℝ) ≤ 2*(1+Real.log L)^m)
    (w : Mom d) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (κ : D → (Fin d → ℤ)) (hκ : M.IsDecoration L w c κ) (hres : M.IsRestricted L γ δ w β k0 κ) :
    let R := (((appbCutSign M S (r.edge p.first).val)⁻¹ : ℤˣ) : ℤ) • (∑ v ∈ S,c v)
    |inner ℝ R (Molecule.kvec L w (r.localLabels κ) p.first)-
      ((((appbCutSign M S (r.edge p.first).val)⁻¹ : ℤˣ) : ℤ)*(∑ v ∈ S,β v)+‖R‖^2)/2| ≤ appbWidth δ γ m L := by
  have hLp := zero_lt_one.trans_le hL
  have hτ : 0 ≤ δ⁻¹*L^(-2*γ) := by positivity
  have he := p.energy_difference hopp L γ δ w c β k0 κ hκ hres
  have hE : |‖Molecule.kvec L w (r.localLabels κ) p.first‖^2-
      ‖Molecule.kvec L w (r.localLabels κ) p.second‖^2-
      (((appbCutSign M S (r.edge p.first).val)⁻¹ : ℤˣ) : ℤ)*(∑ v ∈ S,β v)| ≤ 2*appbWidth δ γ m L := by
    refine he.trans ((mul_le_mul_of_nonneg_right hcard hτ).trans_eq ?_)
    unfold appbWidth
    ring
  exact appb_difference_strip_bound _ _ _ _ _ (p.momentum_difference hopp L w c κ hκ).symm hE

theorem atomic_window_le_log {L γ δ : ℝ} (hL : 1 ≤ L) (hδ : 0 < δ) (m : ℕ) :
    δ⁻¹*L^(-2*γ) ≤ appbWidth δ γ m L := by
  have hLp := zero_lt_one.trans_le hL
  have hlog := Real.log_nonneg hL
  have hp : 1 ≤ (1+Real.log L)^m := one_le_pow₀ (by linarith only [hlog])
  unfold appbWidth
  calc
    _ = δ⁻¹*1*L^(-2*γ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (inv_pos.mpr hδ).le)
      (Real.rpow_nonneg hLp.le _)

end AppbCutPair
end WaveTurbulence.Mole
