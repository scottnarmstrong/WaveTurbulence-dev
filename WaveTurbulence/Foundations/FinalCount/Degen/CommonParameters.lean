/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.RemovalCounting
public import WaveTurbulence.Foundations.Molecule.MoleculeBasic
import Mathlib.Tactic

/-! # Uniform post-removal parameters, determined only by the common label -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Exact degree loss, counting self-loop darts correctly. -/
theorem deg_eraseAtoms_add_removed (M : Molecule V D) (Y : Finset V) {z : V} (hz : z ∉ Y) :
    (eraseAtoms M Y).deg z + (removedDartsAt M Y z).card = M.deg z := by
  have hs := sum_dartsAt_split M Y hz (fun _ => (1 : ℕ))
  simpa only [sum_const, smul_eq_mul, nsmul_eq_mul, mul_one, Molecule.deg] using hs.symm

/-- Updated momenta when every removed bond carries the one vector q. -/
noncomputable def momentumForCommon (M : Molecule V D) {d : ℕ} (Y : Finset V)
    (c : V → Mom d) (q : Mom d) (z : V) : Mom d :=
  c z - (∑ x ∈ removedDartsAt M Y z, M.dartSign x) • q

/-- Updated energy centers for the same common vector. -/
noncomputable def energyForCommon (M : Molecule V D) {d : ℕ} (Y : Finset V)
    (β : V → ℝ) (q : Mom d) (z : V) : ℝ :=
  β z - (∑ x ∈ removedDartsAt M Y z, M.dartSign x) * ‖q‖ ^ 2

/-- Actual deleted labels depend only on the common label at the removed atom. -/
theorem residualMomentum_eq_common (M : Molecule V D) {d : ℕ} {v : V} {e : D}
    (he : M.atom e = v) {L : ℝ} {w : Mom d} {c : V → Mom d} {κ : D → (Fin d → ℤ)}
    (hb : ∀ x, κ (M.mate x) = κ x) (hc : ConstantAt M κ v) :
    residualMomentum M {v} L w c κ = momentumForCommon M {v} c (Molecule.kvec L w κ e) := by
  funext z
  unfold residualMomentum momentumForCommon
  rw [Finset.sum_smul]
  congr 1
  apply sum_congr rfl
  intro x hx
  have hxv : M.atom (M.mate x) = v := mem_singleton.mp (mem_filter.mp hx).2
  rw [Molecule.kvec, removed_value_eq_common M hb hc he (Or.inr hxv)]
  rfl

theorem residualEnergy_eq_common (M : Molecule V D) {d : ℕ} {v : V} {e : D}
    (he : M.atom e = v) {L : ℝ} {w : Mom d} {β : V → ℝ} {κ : D → (Fin d → ℤ)}
    (hb : ∀ x, κ (M.mate x) = κ x) (hc : ConstantAt M κ v) :
    residualEnergy M {v} L w β κ = energyForCommon M {v} β (Molecule.kvec L w κ e) := by
  funext z
  unfold residualEnergy energyForCommon
  rw [Finset.sum_mul]
  congr 1
  apply sum_congr rfl
  intro x hx
  have hxv : M.atom (M.mate x) = v := mem_singleton.mp (mem_filter.mp hx).2
  rw [Molecule.kvec, removed_value_eq_common M hb hc he (Or.inr hxv)]
  rfl

/-- A surviving degree-four atom lost no dart, so its updated momentum
remains zero as required by the exact countE supremum. -/
theorem momentumForCommon_zero_at_four (M : Molecule V D) (hM : M.IsMolecule)
    {d : ℕ} (Y : Finset V) (c : V → Mom d) (q : Mom d)
    (hc : ∀ z ∈ M.atoms, M.deg z = 4 → c z = 0) :
    ∀ z ∈ (eraseAtoms M Y).atoms, (eraseAtoms M Y).deg z = 4 →
      momentumForCommon M Y c q z = 0 := by
  intro z hz hfour
  obtain ⟨hzM, hzY⟩ := mem_sdiff.mp hz
  have hdeg := deg_eraseAtoms_add_removed M Y hzY
  have hcap := Mole.deg_le_four M hM hzM
  have he : (removedDartsAt M Y z).card = 0 := by omega
  have hzfour : M.deg z = 4 := by omega
  unfold momentumForCommon
  rw [card_eq_zero.mp he, sum_empty, zero_smul, sub_zero]
  exact hc z hzM hzfour

end WaveTurbulence.Degen
