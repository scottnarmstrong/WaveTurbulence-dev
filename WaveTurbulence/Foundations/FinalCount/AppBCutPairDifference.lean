/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCutPairEnergy
public import WaveTurbulence.Foundations.FinalCount.AppBSignedPairNormalization
public import WaveTurbulence.Foundations.FinalCount.AppBTripleOrdering
public import WaveTurbulence.Foundations.FinalCount.AppBPairStripAlgebra
import Mathlib.Tactic

/-! # Conserved difference and independent strip from an opposite-sign cut -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbCutPair
variable {M : Molecule V D} {P : AppbPattern} {r : AppbRealization M P} {S : Finset V}
    (p : AppbCutPair r S)
    (hopp : appbCutSign M S (r.edge p.first).val ≠ appbCutSign M S (r.edge p.second).val)
include hopp

theorem momentum_difference {d : ℕ} (L : ℝ) (w : Mom d) (c : V → Mom d)
    (κ : D → (Fin d → ℤ)) (hκ : M.IsDecoration L w c κ) :
    Molecule.kvec L w (r.localLabels κ) p.first-Molecule.kvec L w (r.localLabels κ) p.second =
      (((appbCutSign M S (r.edge p.first).val)⁻¹ : ℤˣ) : ℤ) • (∑ v ∈ S,c v) := by
  have hm := appb_signed_pair_momentum _ _ _ _ _ (p.momentum L w c κ hκ)
  have hmid := appb_units_eq_neg_of_ne _ _ hopp
  simpa [hmid,sub_eq_add_neg] using hm

theorem energy_difference {d : ℕ} (L γ δ : ℝ) (w : Mom d) (c : V → Mom d)
    (β : V → ℝ) (k0 : D → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hres : M.IsRestricted L γ δ w β k0 κ) :
    |‖Molecule.kvec L w (r.localLabels κ) p.first‖^2-‖Molecule.kvec L w (r.localLabels κ) p.second‖^2-
      (((appbCutSign M S (r.edge p.first).val)⁻¹ : ℤˣ) : ℤ)*(∑ v ∈ S,β v)| ≤ S.card*(δ⁻¹*L^(-2*γ)) := by
  have he := appb_signed_pair_energy _ _ _ _ _ _ (p.energy L γ δ w c β k0 κ hκ hres)
  have hmid := appb_units_eq_neg_of_ne _ _ hopp
  simpa [hmid,sub_eq_add_neg] using he

/-- A two-atom cut produces an independent strip with the original atomic
window and a vector and center fixed by the old source parameters. -/
theorem strip_bound {d : ℕ} {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (hδ : 0 < δ)
    (hcard : S.card ≤ 2) (w : Mom d) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (κ : D → (Fin d → ℤ)) (hκ : M.IsDecoration L w c κ) (hres : M.IsRestricted L γ δ w β k0 κ) :
    let R := (((appbCutSign M S (r.edge p.first).val)⁻¹ : ℤˣ) : ℤ) • (∑ v ∈ S,c v)
    |inner ℝ R (Molecule.kvec L w (r.localLabels κ) p.first)-
      ((((appbCutSign M S (r.edge p.first).val)⁻¹ : ℤˣ) : ℤ)*(∑ v ∈ S,β v)+‖R‖^2)/2| ≤ δ⁻¹*L^(-2*γ) := by
  have hτ : 0 ≤ δ⁻¹*L^(-2*γ) := by positivity
  have he := p.energy_difference hopp L γ δ w c β k0 κ hκ hres
  have hc : (S.card : ℝ) ≤ 2 := by exact_mod_cast hcard
  have hE := he.trans (mul_le_mul_of_nonneg_right hc hτ)
  exact appb_difference_strip_bound _ _ _ _ _ (p.momentum_difference hopp L w c κ hκ).symm hE

end AppbCutPair
end WaveTurbulence.Mole
