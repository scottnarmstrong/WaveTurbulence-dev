/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.Degen.Cut
import Mathlib.Tactic

/-! # DH23 section 10.5: the actual atom-deletion map on decorations -/

@[expose] public section
open Finset

namespace WaveTurbulence.Degen

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Darts of bonds retained after removing atoms `Y`. -/
abbrev RetainedDart (M : Molecule V D) (Y : Finset V) :=
  {x : D // M.atom x ∉ Y ∧ M.atom (M.mate x) ∉ Y}

/-- The actual induced pre-molecule after removing `Y` and its incident bonds. -/
def eraseAtoms (M : Molecule V D) (Y : Finset V) : Molecule V (RetainedDart M Y) where
  atoms := M.atoms \ Y
  atom x := M.atom x.val
  mate x := ⟨M.mate x.val, x.property.2, by simpa only [M.mate_mate] using x.property.1⟩
  out x := M.out x.val
  atom_mem x := mem_sdiff.mpr ⟨M.atom_mem x.val, x.property.1⟩
  mate_mate x := Subtype.ext (M.mate_mate x.val)
  mate_ne x h := M.mate_ne x.val (congrArg Subtype.val h)
  out_mate x := M.out_mate x.val

/-- The part of the old local divergence removed at a surviving atom. -/
def removedDartsAt (M : Molecule V D) (Y : Finset V) (v : V) : Finset D :=
  (M.dartsAt v).filter fun x => M.atom (M.mate x) ∈ Y

/-- Exact reindexing of the retained local divergence. -/
theorem sum_dartsAt_eraseAtoms (M : Molecule V D) (Y : Finset V) {v : V} (hv : v ∉ Y)
    {E : Type*} [AddCommMonoid E] (g : D → E) :
    (∑ x ∈ (eraseAtoms M Y).dartsAt v, g x.val) =
      ∑ x ∈ (M.dartsAt v).filter (fun x => M.atom (M.mate x) ∉ Y), g x := by
  classical
  apply sum_bij (fun x _ => x.val)
  · intro x hx
    have hx' : M.atom x.val = v := (mem_filter.mp hx).2
    simp only [mem_filter, Molecule.dartsAt, mem_univ, true_and]
    exact ⟨hx', x.property.2⟩
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro x hx
    obtain ⟨hxat, hxY⟩ := mem_filter.mp hx
    have hxv : M.atom x = v := (mem_filter.mp hxat).2
    have hxr : M.atom x ∉ Y := by simpa only [hxv] using hv
    refine ⟨⟨x, hxr, hxY⟩, ?_, rfl⟩
    simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and]
    exact hxv
  · intro x _
    rfl

/-- Exact splitting of a local signed sum into retained and removed darts. -/
theorem sum_dartsAt_split (M : Molecule V D) (Y : Finset V) {v : V} (hv : v ∉ Y)
    {E : Type*} [AddCommMonoid E] (g : D → E) :
    (∑ x ∈ M.dartsAt v, g x) =
      (∑ x ∈ (eraseAtoms M Y).dartsAt v, g x.val) + ∑ x ∈ removedDartsAt M Y v, g x := by
  classical
  rw [sum_dartsAt_eraseAtoms M Y hv]
  have hh := sum_filter_add_sum_filter_not (M.dartsAt v) (fun x => M.atom (M.mate x) ∈ Y) g
  unfold removedDartsAt
  exact (add_comm _ _).trans hh |>.symm

/-- The source's new atom parameters, determined by the deleted labels. -/
noncomputable def residualMomentum (M : Molecule V D) {d : ℕ} (Y : Finset V)
    (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ)) (v : V) : Mom d :=
  c v - ∑ x ∈ removedDartsAt M Y v, M.dartSign x • Molecule.kvec L w κ x

/-- DH23 section 10.5(4): deletion sends every actual decoration to an
actual decoration with the explicitly updated atom parameters. -/
theorem isDecoration_eraseAtoms (M : Molecule V D) {d : ℕ} (Y : Finset V)
    {L : ℝ} {w : Mom d} {c : V → Mom d} {κ : D → (Fin d → ℤ)}
    (hκ : M.IsDecoration L w c κ) :
    (eraseAtoms M Y).IsDecoration L w (residualMomentum M Y L w c κ) (fun x => κ x.val) := by
  constructor
  · intro x
    exact hκ.1 x.val
  · intro v hv
    have hv' : v ∈ M.atoms ∧ v ∉ Y := mem_sdiff.mp hv
    have hs := sum_dartsAt_split M Y hv'.2 (fun x => M.dartSign x • Molecule.kvec L w κ x)
    rw [hκ.2 v hv'.1] at hs
    change (∑ x ∈ (eraseAtoms M Y).dartsAt v, M.dartSign x.val • Molecule.kvec L w κ x.val) = _
    unfold residualMomentum
    exact eq_sub_iff_add_eq.mpr hs.symm

/-- The explicitly updated energy centers after deleting atoms. -/
noncomputable def residualEnergy (M : Molecule V D) {d : ℕ} (Y : Finset V)
    (L : ℝ) (w : Mom d) (β : V → ℝ) (κ : D → (Fin d → ℤ)) (v : V) : ℝ :=
  β v - ∑ x ∈ removedDartsAt M Y v, M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2

/-- Restriction preserves the exact energy tolerance and every unit-ball
localization, with concrete updated energy parameters. -/
theorem isRestricted_eraseAtoms (M : Molecule V D) {d : ℕ} (Y : Finset V)
    {L γ δ : ℝ} {w : Mom d} {β : V → ℝ} {κ : D → (Fin d → ℤ)} {k0 : D → Mom d}
    (hres : M.IsRestricted L γ δ w β k0 κ) :
    (eraseAtoms M Y).IsRestricted L γ δ w (residualEnergy M Y L w β κ)
      (fun x => k0 x.val) (fun x => κ x.val) := by
  constructor
  · intro v hv
    have hv' := mem_sdiff.mp hv
    have hs := sum_dartsAt_split M Y hv'.2 (fun x => M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2)
    have he : (eraseAtoms M Y).Gamma L w (fun x => κ x.val) v - residualEnergy M Y L w β κ v =
        M.Gamma L w κ v - β v := by
      change (∑ x ∈ (eraseAtoms M Y).dartsAt v, M.dartSign x.val * ‖Molecule.kvec L w κ x.val‖ ^ 2) -
        (β v - _) = _
      change M.Gamma L w κ v = _ at hs
      rw [hs]
      ring
    rw [he]
    exact hres.1 v hv'.1
  · intro x
    exact hres.2 x.val

end WaveTurbulence.Degen
