/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrame
import Mathlib.Tactic

/-! # Ordered triple constraints inside a larger local operation -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
theorem appb_sum_fin_three_permutation {E : Type*} [AddCommMonoid E]
    (π : Equiv.Perm (Fin 3)) (f : Fin 3 → E) :
    (∑ i,f i) = f (π 0)+f (π 1)+f (π 2) := by
  calc
    _ = ∑ i : Fin 3,f (π i) := (Equiv.sum_comp π f).symm
    _ = _ := Fin.sum_univ_three _

namespace AppbTripleFrame
variable {M : Molecule V D} {P : AppbPattern} {r : AppbRealization M P} {v : V}
    (t : AppbTripleFrame r v) (π : Equiv.Perm (Fin 3))
    (hsame : appbIncidenceSign M v (r.edge (t.index (π 0))).val =
      appbIncidenceSign M v (r.edge (t.index (π 2))).val)
    (hopp : appbIncidenceSign M v (r.edge (t.index (π 0))).val ≠
      appbIncidenceSign M v (r.edge (t.index (π 1))).val)

include hsame hopp

theorem momentum {d : ℕ} (hv : v ∈ r.removedAtoms) (L : ℝ) (w : Mom d)
    (c : V → Mom d) (κ : D → (Fin d → ℤ)) (hκ : M.IsDecoration L w c κ) :
    Molecule.kvec L w (r.localLabels κ) (t.index (π 0))-
      Molecule.kvec L w (r.localLabels κ) (t.index (π 1))+
      Molecule.kvec L w (r.localLabels κ) (t.index (π 2)) =
        (((appbIncidenceSign M v (r.edge (t.index (π 0))).val)⁻¹ : ℤˣ) : ℤ) • c v := by
  have hm := r.local_momentum L w c κ hκ hv
  rw [t.sum_incidence,appb_sum_fin_three_permutation π] at hm
  have hmid := appb_units_eq_neg_of_ne _ _ hopp
  apply appb_signed_triple_momentum (appbIncidenceSign M v (r.edge (t.index (π 0))).val)
  simpa only [hmid,← hsame,Units.val_neg,neg_smul,sub_eq_add_neg] using hm

theorem energy {d : ℕ} (hv : v ∈ r.removedAtoms) (L γ δ : ℝ) (w : Mom d)
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hres : M.IsRestricted L γ δ w β k0 κ) :
    |‖Molecule.kvec L w (r.localLabels κ) (t.index (π 0))‖^2-
      ‖Molecule.kvec L w (r.localLabels κ) (t.index (π 1))‖^2+
      ‖Molecule.kvec L w (r.localLabels κ) (t.index (π 2))‖^2-
      (((appbIncidenceSign M v (r.edge (t.index (π 0))).val)⁻¹ : ℤˣ) : ℤ)*β v| ≤ δ⁻¹*L^(-2*γ) := by
  have he := r.local_energy L γ δ w c β k0 κ hκ hres hv
  rw [t.sum_incidence,appb_sum_fin_three_permutation π] at he
  simp only [zsmul_eq_mul] at he
  have hmid := appb_units_eq_neg_of_ne _ _ hopp
  apply appb_signed_triple_energy (appbIncidenceSign M v (r.edge (t.index (π 0))).val)
  simpa only [hmid,← hsame,Units.val_neg,Int.cast_neg,neg_mul,sub_eq_add_neg] using he

end AppbTripleFrame
end WaveTurbulence.Mole
