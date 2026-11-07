/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairSourceEquations
public import WaveTurbulence.Foundations.Molecule.Degen.Cut
import Mathlib.Tactic

/-! # Literal boundary-label source equations for the good operations

The boundary enumeration is an actual equivalence with the old cut, and
the integer charge comes from a counted reference decoration. No charge
at a four-valent atom is assumed to vanish.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem sum_boundary_eq_ordered (M : Molecule V D) (U : Finset V) {r : ℕ}
    (e : Fin r ≃ {x // x ∈ Degen.boundaryDarts M U})
    {A : Type*} [AddCommMonoid A] (g : D → A) :
    (∑ i, g (e i).val) = ∑ x ∈ Degen.boundaryDarts M U, g x := by
  apply sum_bij (fun i _ => (e i).val)
  · intro i _
    exact (e i).property
  · intro i _ j _ hh
    exact e.injective (Subtype.ext hh)
  · intro x hx
    obtain ⟨i,hi⟩ := e.surjective ⟨x,hx⟩
    exact ⟨i,mem_univ _,congrArg Subtype.val hi⟩
  · intro i _; rfl

def boundaryIntegerCharge (M : Molecule V D) (U : Finset V) {r d : ℕ}
    (e : Fin r ≃ {x // x ∈ Degen.boundaryDarts M U}) (κ : D → (Fin d → ℤ)) : Fin d → ℤ :=
  ∑ i, doubleSign (M.out (e i).val) • κ (e i).val

theorem ordered_boundary_momentum (M : Molecule V D) {d : ℕ} (L : ℝ)
    (U : Finset V) (hU : U ⊆ M.atoms) {r : ℕ}
    (e : Fin r ≃ {x // x ∈ Degen.boundaryDarts M U})
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} (hd : M.IsDecoration L (0 : Mom d) c κ) :
    (∑ i, M.dartSign (e i).val • latticePoint L (κ (e i).val)) = ∑ v ∈ U, c v := by
  have hh := Degen.cut_momentum M hd U hU
  rw [← sum_boundary_eq_ordered M U e (fun x => M.dartSign x • Molecule.kvec L (0 : Mom d) κ x)] at hh
  simpa only [Molecule.kvec,zero_add] using hh

theorem ordered_boundary_energy (M : Molecule V D) {d : ℕ} (L γ δ : ℝ)
    (U : Finset V) (hU : U ⊆ M.atoms) {r : ℕ}
    (e : Fin r ≃ {x // x ∈ Degen.boundaryDarts M U})
    {c : V → Mom d} {κ : D → (Fin d → ℤ)} {β : V → ℝ} {k0 : D → Mom d}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hr : M.IsRestricted L γ δ (0 : Mom d) β k0 κ) :
    |(∑ i, M.dartSign (e i).val * ‖latticePoint L (κ (e i).val)‖^2)-∑ v ∈ U, β v| ≤
      (U.card : ℝ)*(δ⁻¹*L^(-2*γ)) := by
  have hh := Degen.cut_energy M hd hr U hU
  rw [← sum_boundary_eq_ordered M U e (fun x => M.dartSign x * ‖Molecule.kvec L (0 : Mom d) κ x‖^2)] at hh
  simpa only [Molecule.kvec,zero_add] using hh

theorem boundaryIntegerCharge_eq (M : Molecule V D) {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    (U : Finset V) (hU : U ⊆ M.atoms) {r : ℕ}
    (e : Fin r ≃ {x // x ∈ Degen.boundaryDarts M U})
    {c : V → Mom d} {κ κ0 : D → (Fin d → ℤ)}
    (hd : M.IsDecoration L (0 : Mom d) c κ) (hd0 : M.IsDecoration L (0 : Mom d) c κ0) :
    boundaryIntegerCharge M U e κ = boundaryIntegerCharge M U e κ0 := by
  apply latticePointHom_injective hL
  change latticePointHom L (∑ i, doubleSign (M.out (e i).val) • κ (e i).val) =
    latticePointHom L (∑ i, doubleSign (M.out (e i).val) • κ0 (e i).val)
  simp only [map_sum,map_zsmul,latticePointHom_apply,doubleSign_out_smul]
  exact (ordered_boundary_momentum M L U hU e hd).trans
    (ordered_boundary_momentum M L U hU e hd0).symm

end WaveTurbulence.MoleProp
