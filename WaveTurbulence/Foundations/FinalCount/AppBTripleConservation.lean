/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLocalTriple
import Mathlib.Tactic

/-! # Signed triple momentum and energy from actual source conservation -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbLocalTriple
variable {M : Molecule V D} {P : AppbPattern} {r : AppbRealization M P} {v : V}
    (t : AppbLocalTriple r v)

theorem momentum {d : ℕ} (hv : v ∈ r.removedAtoms) (L : ℝ) (w : Mom d)
    (c : V → Mom d) (κ : D → (Fin d → ℤ)) (hκ : M.IsDecoration L w c κ) :
    Molecule.kvec L w (r.localLabels κ) t.first-
      Molecule.kvec L w (r.localLabels κ) t.middle+
      Molecule.kvec L w (r.localLabels κ) t.last =
        (((appbIncidenceSign M v (r.edge t.first).val)⁻¹ : ℤˣ) : ℤ) • c v := by
  have hm := r.local_momentum L w c κ hκ hv
  rw [t.sum_three] at hm
  simp only [appb_incidence_sign_eq M v _ (t.incidence _)] at hm
  have hmid := appb_units_eq_neg_of_ne _ _ t.opposite_sign
  apply appb_signed_triple_momentum (appbIncidenceSign M v (r.edge t.first).val)
  simpa only [hmid,← t.same_sign,Units.val_neg,neg_smul,sub_eq_add_neg] using hm

theorem energy {d : ℕ} (hv : v ∈ r.removedAtoms) (L γ δ : ℝ) (w : Mom d)
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hres : M.IsRestricted L γ δ w β k0 κ) :
    |‖Molecule.kvec L w (r.localLabels κ) t.first‖^2-
      ‖Molecule.kvec L w (r.localLabels κ) t.middle‖^2+
      ‖Molecule.kvec L w (r.localLabels κ) t.last‖^2-
      (((appbIncidenceSign M v (r.edge t.first).val)⁻¹ : ℤˣ) : ℤ)*β v| ≤ δ⁻¹*L^(-2*γ) := by
  have he := r.local_energy L γ δ w c β k0 κ hκ hres hv
  rw [t.sum_three] at he
  simp only [appb_incidence_sign_eq M v _ (t.incidence _),zsmul_eq_mul] at he
  have hmid := appb_units_eq_neg_of_ne _ _ t.opposite_sign
  apply appb_signed_triple_energy (appbIncidenceSign M v (r.edge t.first).val)
  simpa only [hmid,← t.same_sign,Units.val_neg,Int.cast_neg,neg_mul,sub_eq_add_neg] using he

end AppbLocalTriple
end WaveTurbulence.Mole
