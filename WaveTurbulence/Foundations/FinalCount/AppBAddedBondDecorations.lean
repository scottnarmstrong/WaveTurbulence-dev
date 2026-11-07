/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBAddedBondSums
import Mathlib.Tactic

/-! # Exact momentum and energy transport for bond reinsertion

The source Appendix B permits arbitrary degree-four centers. The new
centers below are explicit functions of the removed boundary labels.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Extend a bond-constant label assignment by a new physical bond. -/
def appbAddedLabels {K : Type*} (κ : D → K) (q : K) : D ⊕ Bool → K :=
  Sum.elim κ (fun _ => q)

noncomputable def appbAddedMomentum {d : ℕ} (a b : V) (L : ℝ) (w : Mom d)
    (q : Fin d → ℤ) (c : V → Mom d) (v : V) : Mom d :=
  c v + (if a = v then w+latticePoint L q else 0) -
    (if b = v then w+latticePoint L q else 0)

noncomputable def appbAddedEnergy (a b : V) {d : ℕ} (L : ℝ) (w : Mom d)
    (q : Fin d → ℤ) (β : V → ℝ) (v : V) : ℝ :=
  β v + (if a = v then ‖w+latticePoint L q‖^2 else 0) -
    (if b = v then ‖w+latticePoint L q‖^2 else 0)

/-- Actual momentum conservation under reinsertion, with concrete centers. -/
theorem appb_isDecoration_addBond (M : Molecule V D) (a b : V)
    (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) {d : ℕ} {L : ℝ} {w : Mom d}
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} (q : Fin d → ℤ)
    (hκ : M.IsDecoration L w c κ) :
    (addBond M a b).IsDecoration L w (appbAddedMomentum a b L w q c) (appbAddedLabels κ q) := by
  constructor
  · rintro (x|t)
    · exact hκ.1 x
    · rfl
  · intro v hv
    have hvM : v ∈ M.atoms := by
      change v ∈ insert a (insert b M.atoms) at hv
      simpa only [insert_eq_of_mem hb,insert_eq_of_mem ha] using hv
    rw [appb_sum_dartsAt_addBond]
    change (∑ x ∈ M.dartsAt v, M.dartSign x • Molecule.kvec L w κ x) +
      (if a = v then (1 : ℝ) • (w+latticePoint L q) else 0) +
      (if b = v then (-1 : ℝ) • (w+latticePoint L q) else 0) = _
    rw [hκ.2 v hvM]
    by_cases ha' : a = v <;> by_cases hb' : b = v
    all_goals simp [appbAddedMomentum,ha',hb',sub_eq_add_neg,add_comm]

/-- Energy centers shift by the exact added signed squared norm. -/
theorem appb_Gamma_addBond (M : Molecule V D) (a b : V) {d : ℕ} (L : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) (q : Fin d → ℤ) (v : V) :
    (addBond M a b).Gamma L w (appbAddedLabels κ q) v =
      M.Gamma L w κ v + (if a = v then ‖w+latticePoint L q‖^2 else 0) -
        (if b = v then ‖w+latticePoint L q‖^2 else 0) := by
  unfold Molecule.Gamma
  rw [appb_sum_dartsAt_addBond]
  change (∑ x ∈ M.dartsAt v, M.dartSign x * ‖Molecule.kvec L w κ x‖^2) +
    (if a = v then (1 : ℝ) * ‖w+latticePoint L q‖^2 else 0) +
    (if b = v then (-1 : ℝ) * ‖w+latticePoint L q‖^2 else 0) = _
  by_cases ha' : a = v <;> by_cases hb' : b = v
  all_goals simp [ha',hb',sub_eq_add_neg,add_comm]

/-- Literal restrictions are preserved, without increasing the energy
window. The new bond is localized at its assigned physical momentum. -/
theorem appb_isRestricted_addBond (M : Molecule V D) (a b : V)
    (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) {d : ℕ} {L γ δ : ℝ} {w : Mom d}
    {β : V → ℝ} {κ : D → (Fin d → ℤ)} {k0 : D → Mom d} (q : Fin d → ℤ)
    (hκ : M.IsRestricted L γ δ w β k0 κ) :
    (addBond M a b).IsRestricted L γ δ w (appbAddedEnergy a b L w q β)
      (appbAddedLabels k0 (w+latticePoint L q)) (appbAddedLabels κ q) := by
  constructor
  · intro v hv
    have hvM : v ∈ M.atoms := by
      change v ∈ insert a (insert b M.atoms) at hv
      simpa only [insert_eq_of_mem hb,insert_eq_of_mem ha] using hv
    rw [appb_Gamma_addBond]
    have he : M.Gamma L w κ v + (if a = v then ‖w+latticePoint L q‖^2 else 0) -
        (if b = v then ‖w+latticePoint L q‖^2 else 0) - appbAddedEnergy a b L w q β v =
        M.Gamma L w κ v - β v := by unfold appbAddedEnergy; ring
    rw [he]
    exact hκ.1 v hvM
  · rintro (x|t)
    · exact hκ.2 x
    · change ‖(w+latticePoint L q)-(w+latticePoint L q)‖ ≤ 1
      simp

end WaveTurbulence.Mole
