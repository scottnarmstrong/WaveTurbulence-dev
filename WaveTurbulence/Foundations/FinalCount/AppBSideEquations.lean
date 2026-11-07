/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBClosedSide
import Mathlib.Tactic

/-! # Exact conservation and energy equations on a closed component side -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_side_momentum_sum (M : Molecule V D) (S : Finset V) (h : AppbClosedSide M S)
    {d : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) {v : V} (hv : v ∈ S) :
    (∑ x ∈ (appbSideMolecule M S h).dartsAt v,
      (appbSideMolecule M S h).dartSign x • Molecule.kvec L w (appbSideLabels M S κ) x) =
      ∑ x ∈ M.dartsAt v,M.dartSign x • Molecule.kvec L w κ x :=
  appb_sum_dartsAt_side M S h (fun x => M.dartSign x • Molecule.kvec L w κ x) hv

theorem appb_side_Gamma_eq (M : Molecule V D) (S : Finset V) (h : AppbClosedSide M S)
    {d : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) {v : V} (hv : v ∈ S) :
    (appbSideMolecule M S h).Gamma L w (appbSideLabels M S κ) v = M.Gamma L w κ v :=
  appb_sum_dartsAt_side M S h (fun x => M.dartSign x * ‖Molecule.kvec L w κ x‖^2) hv

@[expose] noncomputable def appbSideParameters {M : Molecule V D} (S : Finset V) (h : AppbClosedSide M S)
    {d : ℕ} (p : AppbCountParameters M d) : AppbCountParameters (appbSideMolecule M S h) d where
  momentum := p.momentum
  energy := p.energy
  center := fun x => p.center x.val
  center_mate := fun x => p.center_mate x.val

/-- No source parameter changes on a closed side. -/
theorem appb_isDecoration_side {M : Molecule V D} (S : Finset V) (h : AppbClosedSide M S)
    {d : ℕ} (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) :
    (appbSideMolecule M S h).IsDecoration L w c (appbSideLabels M S κ) := by
  refine ⟨fun x => hκ.1 x.val,?_⟩
  intro v hv
  rw [appb_side_momentum_sum M S h L w κ hv]
  exact hκ.2 v (h.subset_atoms hv)

theorem appb_isRestricted_side {M : Molecule V D} (S : Finset V) (h : AppbClosedSide M S)
    {d : ℕ} (L γ δ : ℝ) (w : Mom d) (β : V → ℝ) (k0 : D → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsRestricted L γ δ w β k0 κ) :
    (appbSideMolecule M S h).IsRestricted L γ δ w β (fun x => k0 x.val) (appbSideLabels M S κ) := by
  constructor
  · intro v hv
    rw [appb_side_Gamma_eq M S h L w κ hv]
    exact hκ.1 v (h.subset_atoms hv)
  · intro x
    exact hκ.2 x.val

end WaveTurbulence.Mole
