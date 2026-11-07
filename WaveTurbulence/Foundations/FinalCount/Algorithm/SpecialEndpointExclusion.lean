/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBBranchConditions
public import WaveTurbulence.Foundations.FinalCount.AppBStatistics
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
import Mathlib.Tactic

/-! # Excluding special endpoints from actual single-neighbor degrees -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem special_endpoints_ne_of_no_three_single_neighbor (M : Molecule V D) (hno : AppbNoLoops M)
    {a : V} (hn : ∀ b ∈ M.atoms,a ≠ b → M.bondsBetween a b = 1 → M.deg b ≠ 3)
    {x : D} (hs : AppbSpecial M x) : M.atom x ≠ a ∧ M.atom (M.mate x) ≠ a := by
  obtain ⟨ho,hd1,hd2,c,hc,d,hd,hcd,hca,hcb,hda,hdb,hcentral,hA,hB⟩ := hs
  constructor
  · intro he
    have hm : M.bondsBetween a (M.atom (M.mate x)) = 1 := he ▸ hcentral
    exact hn _ (M.atom_mem _) (by rw [← he]; exact hno x) hm hd2
  · intro he
    have hm : M.bondsBetween a (M.atom x) = 1 := by
      rw [← he,bondsBetween_symm]
      exact hcentral
    exact hn _ (M.atom_mem _) (by rw [← he]; exact Ne.symm (hno x)) hm hd1

end WaveTurbulence.Mole.AppbAlgorithm
