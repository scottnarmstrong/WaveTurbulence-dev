/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCutPair
public import WaveTurbulence.Foundations.FinalCount.AppBOutgoingCutEnergy
import Mathlib.Tactic

/-! # Energy windows for an actual two-bond cut -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbCutPair
variable {M : Molecule V D} {P : AppbPattern} {r : AppbRealization M P} {S : Finset V}
    (p : AppbCutPair r S)

theorem energy {d : ℕ} (L γ δ : ℝ) (w : Mom d) (c : V → Mom d)
    (β : V → ℝ) (k0 : D → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hres : M.IsRestricted L γ δ w β k0 κ) :
    |(appbCutSign M S (r.edge p.first).val : ℤ)*‖Molecule.kvec L w (r.localLabels κ) p.first‖^2+
      (appbCutSign M S (r.edge p.second).val : ℤ)*‖Molecule.kvec L w (r.localLabels κ) p.second‖^2-
      ∑ v ∈ S,β v| ≤ S.card*(δ⁻¹*L^(-2*γ)) := by
  have he := r.cut_energy S p.subset_atoms p.crossing L γ δ w c β k0 κ hκ hres
  rw [sum_eq_add_of_mem p.first p.second (mem_univ _) (mem_univ _) p.distinct] at he
  · simpa only [appb_cut_sign_eq M S _ p.first_cross,
      appb_cut_sign_eq M S _ p.second_cross,zsmul_eq_mul] using he
  · intro i hi hne
    have hh := p.other i hne.1 hne.2
    by_cases ha : M.atom (r.edge i).val ∈ S
    · simp only [ha,hh.mp ha,ite_true,sub_self]
    · have hb : M.atom (M.mate (r.edge i).val) ∉ S := fun hb => ha (hh.mpr hb)
      simp only [ha,hb,ite_false,sub_zero]

end AppbCutPair
end WaveTurbulence.Mole
