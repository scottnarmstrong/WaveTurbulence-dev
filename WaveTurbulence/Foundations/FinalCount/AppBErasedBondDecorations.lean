/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBErasedBondSums
public import WaveTurbulence.Foundations.FinalCount.AppBFiniteCounts
import Mathlib.Tactic

/-! # Explicit conservation and energy parameters after bond erasure -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbErasedMomentum (M : Molecule V D) (e : D) {d : ℕ}
    (L : ℝ) (w : Mom d) (q : Fin d → ℤ) (c : V → Mom d) (v : V) : Mom d :=
  c v - (if M.atom e = v then M.dartSign e • (w+latticePoint L q) else 0) -
    (if M.atom (M.mate e) = v then M.dartSign (M.mate e) • (w+latticePoint L q) else 0)

noncomputable def appbErasedEnergy (M : Molecule V D) (e : D) {d : ℕ}
    (L : ℝ) (w : Mom d) (q : Fin d → ℤ) (β : V → ℝ) (v : V) : ℝ :=
  β v - (if M.atom e = v then M.dartSign e * ‖w+latticePoint L q‖^2 else 0) -
    (if M.atom (M.mate e) = v then M.dartSign (M.mate e) * ‖w+latticePoint L q‖^2 else 0)

/-- Exact momentum transport with the removed bond label fixed. -/
theorem appb_isDecoration_eraseBond (M : Molecule V D) (e : D) {d : ℕ}
    {L : ℝ} {w : Mom d} {c : V → Mom d} {κ : D → (Fin d → ℤ)} {q : Fin d → ℤ}
    (hκ : M.IsDecoration L w c κ) (hq : κ e = q) :
    (eraseBond M e).IsDecoration L w (appbErasedMomentum M e L w q c) (fun x => κ x.val) := by
  constructor
  · intro x
    exact hκ.1 x.val
  · intro v hv
    have hs := appb_sum_dartsAt_bond_split M e v (fun x => M.dartSign x • Molecule.kvec L w κ x)
    rw [hκ.2 v hv] at hs
    simp only [Molecule.kvec,hκ.1 e,hq] at hs
    change (∑ x ∈ (eraseBond M e).dartsAt v,
      (eraseBond M e).dartSign x • Molecule.kvec L w (fun x => κ x.val) x) + _ + _ = _ at hs
    unfold appbErasedMomentum
    apply eq_sub_iff_add_eq.mpr
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_assoc,add_comm,add_left_comm] using hs

/-- Exact energy/localizer transport with unchanged tolerance. -/
theorem appb_isRestricted_eraseBond (M : Molecule V D) (e : D) {d : ℕ}
    {L γ δ : ℝ} {w : Mom d} {β : V → ℝ} {κ : D → (Fin d → ℤ)} {k0 : D → Mom d} {q : Fin d → ℤ}
    (hκ : ∀ x, κ (M.mate x) = κ x) (hr : M.IsRestricted L γ δ w β k0 κ) (hq : κ e = q) :
    (eraseBond M e).IsRestricted L γ δ w (appbErasedEnergy M e L w q β)
      (fun x => k0 x.val) (fun x => κ x.val) := by
  constructor
  · intro v hv
    have hs := appb_sum_dartsAt_bond_split M e v (fun x => M.dartSign x * ‖Molecule.kvec L w κ x‖^2)
    change (eraseBond M e).Gamma L w (fun x => κ x.val) v + _ + _ = M.Gamma L w κ v at hs
    simp only [Molecule.kvec,hκ e,hq] at hs
    have he : (eraseBond M e).Gamma L w (fun x => κ x.val) v - appbErasedEnergy M e L w q β v =
        M.Gamma L w κ v - β v := by
      unfold appbErasedEnergy
      linarith only [hs]
    rw [he]
    exact hr.1 v hv
  · intro x
    exact hr.2 x.val

/-- Concrete post parameters for the bridge counting comparison. -/
noncomputable def appbErasedBondParameters (M : Molecule V D) (e : D) {d : ℕ}
    (p : AppbCountParameters M d) (L : ℝ) (w : Mom d) (q : Fin d → ℤ) :
    AppbCountParameters (eraseBond M e) d where
  momentum := appbErasedMomentum M e L w q p.momentum
  energy := appbErasedEnergy M e L w q p.energy
  center := fun x => p.center x.val
  center_mate := fun x => p.center_mate x.val

end WaveTurbulence.Mole
