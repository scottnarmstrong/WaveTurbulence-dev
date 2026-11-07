/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.Degen.Removal
import Mathlib.Tactic

/-! # The boundary identity for an atom set (DH21 Lemma 9.14, general form)

For a decoration of a molecule `N` and a set `Y` of its atoms, the sum of the conservation charges over `Y` equals the
signed sum of the vectors of the bonds leaving `Y`; the same holds for the energies `Γ_v`. Internal bonds cancel in
pairs (the two darts of a bond have opposite signs and the same label). DH23 uses this for the (Y) sequences
(L1954, L1956: "`k_{ℓ₁} − k_{ℓ₂}` is fixed and `|k_{ℓ₁}|² − |k_{ℓ₂}|²` is fixed up to distance `δ⁻¹L^{-2γ}`").
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The darts leaving `Y`: their atom is in `Y`, their mate's atom is not. -/
def crossDarts (N : Molecule V D) (Y : Finset V) : Finset D :=
  univ.filter fun x => N.atom x ∈ Y ∧ N.atom (N.mate x) ∉ Y

theorem mem_crossDarts {N : Molecule V D} {Y : Finset V} {x : D} :
    x ∈ crossDarts N Y ↔ N.atom x ∈ Y ∧ N.atom (N.mate x) ∉ Y := by
  simp [crossDarts]

omit [DecidableEq V] [Fintype D] in
theorem dartSign_mate (N : Molecule V D) (x : D) : N.dartSign (N.mate x) = -N.dartSign x := by
  unfold Molecule.dartSign
  rw [N.out_mate x]
  cases N.out x <;> norm_num

/-- Summing a function of darts over the stars of the atoms of `Y`. -/
theorem sum_stars_eq (N : Molecule V D) (Y : Finset V) {E : Type*} [AddCommMonoid E] (f : D → E) :
    ∑ v ∈ Y, ∑ x ∈ N.dartsAt v, f x = ∑ x ∈ univ.filter (fun x => N.atom x ∈ Y), f x := by
  rw [← sum_fiberwise_of_maps_to (s := univ.filter (fun x => N.atom x ∈ Y)) (t := Y) (g := N.atom)
    (fun x hx => (mem_filter.mp hx).2)]
  refine sum_congr rfl fun v hv => sum_congr ?_ fun _ _ => rfl
  ext x
  simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and]
  constructor
  · intro h; exact ⟨h ▸ hv, h⟩
  · intro h; exact h.2

/-- An odd function of darts (`f (mate x) = - f x`) sums to zero over the internal darts of `Y`. -/
theorem sum_internal_eq_zero (N : Molecule V D) (Y : Finset V) {E : Type*} [AddCommGroup E] (f : D → E)
    (hf : ∀ x, f (N.mate x) = -f x) :
    ∑ x ∈ univ.filter (fun x => N.atom x ∈ Y ∧ N.atom (N.mate x) ∈ Y), f x = 0 := by
  refine sum_involution (fun x _ => N.mate x) (fun x _ => by rw [hf x, add_neg_cancel]) ?_ ?_ ?_
  · intro x _ _
    exact N.mate_ne x
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [N.mate_mate]
    exact ⟨hx.2, hx.1⟩
  · intro x _
    exact N.mate_mate x

/-- The star sum over `Y` of an odd function of darts is its sum over the darts leaving `Y`. -/
theorem sum_stars_eq_cross (N : Molecule V D) (Y : Finset V) {E : Type*} [AddCommGroup E] (f : D → E)
    (hf : ∀ x, f (N.mate x) = -f x) :
    ∑ v ∈ Y, ∑ x ∈ N.dartsAt v, f x = ∑ x ∈ crossDarts N Y, f x := by
  rw [sum_stars_eq, ← sum_filter_add_sum_filter_not _ (fun x => N.atom (N.mate x) ∈ Y)]
  have h0 := sum_internal_eq_zero N Y f hf
  rw [filter_filter] at ⊢
  rw [h0, zero_add, filter_filter]
  rfl

/-- **Boundary identity, momentum** (DH21 Lemma 9.14): `∑_{v ∈ Y} c_v = ∑_{x ∈ ∂Y} ζ_x k_x`. -/
theorem sum_charges_eq_cross {N : Molecule V D} {d : ℕ} {L : ℝ} {w : Mom d} {c : V → Mom d}
    {κ : D → (Fin d → ℤ)} (hκ : N.IsDecoration L w c κ) {Y : Finset V} (hY : Y ⊆ N.atoms) :
    ∑ v ∈ Y, c v = ∑ x ∈ crossDarts N Y, N.dartSign x • Molecule.kvec L w κ x := by
  rw [← sum_stars_eq_cross N Y (fun x => N.dartSign x • Molecule.kvec L w κ x)]
  · exact sum_congr rfl fun v hv => (hκ.2 v (hY hv)).symm
  · intro x
    simp only [dartSign_mate, Molecule.kvec, hκ.1 x, neg_smul]

/-- **Boundary identity, energy**: `∑_{v ∈ Y} Γ_v = ∑_{x ∈ ∂Y} ζ_x |k_x|²`. -/
theorem sum_gamma_eq_cross (N : Molecule V D) {d : ℕ} (L : ℝ) (w : Mom d) {κ : D → (Fin d → ℤ)}
    (hκ : ∀ x, κ (N.mate x) = κ x) (Y : Finset V) :
    ∑ v ∈ Y, N.Gamma L w κ v = ∑ x ∈ crossDarts N Y, N.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2 := by
  unfold Molecule.Gamma
  rw [sum_stars_eq_cross N Y (fun x => N.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2)]
  intro x
  simp only [dartSign_mate, Molecule.kvec, hκ x, neg_mul]

end WaveTurbulence.MoleProp4
