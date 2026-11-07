/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBClosedSidePaths
public import WaveTurbulence.Foundations.FinalCount.AppBLinks
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
import Mathlib.Tactic

/-! # Closed-side restriction preserves every internal bond and direction -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem bondsBetween_closed_side (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    {a b : V} (ha : a ∈ S) (hb : b ∈ S) :
    (appbSideMolecule M S hS).bondsBetween a b = M.bondsBetween a b := by
  unfold Molecule.bondsBetween
  apply card_bij (fun x _ => x.val)
  · intro x hx
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(mem_filter.mp (mem_filter.mp hx).1).2⟩,
      (mem_filter.mp hx).2⟩
  · intro x hx y hy he
    exact Subtype.ext he
  · intro x hx
    have he := (mem_filter.mp hx).2
    have hmem : M.atom x ∈ S := by
      rcases Sym2.eq_iff.mp he with he | he
      · exact he.1.symm ▸ ha
      · exact he.1.symm ▸ hb
    refine ⟨⟨x,hmem⟩,?_,rfl⟩
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(mem_filter.mp (mem_filter.mp hx).1).2⟩,he⟩

theorem directed_closed_side_iff (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    {a b : V} (ha : a ∈ S) :
    (appbSideMolecule M S hS).Directed a b ↔ M.Directed a b := by
  constructor
  · rintro ⟨x,ho,hx,hy⟩
    exact ⟨x.val,ho,hx,hy⟩
  · rintro ⟨x,ho,hx,hy⟩
    exact ⟨⟨x,hx.symm ▸ ha⟩,ho,hx,hy⟩

/-- This equivalence keeps the exact selected rung/rail convention,
including the opposite directions and permitted extra end chords. -/
theorem sourceLadder_closed_side_iff (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    {m : ℕ} (u v : Fin (m+1) → V) :
    Degen.SourceLadder (appbSideMolecule M S hS) u v ↔
      Degen.SourceLadder M u v ∧ (∀ i,u i ∈ S ∧ v i ∈ S) := by
  constructor
  · intro h
    refine ⟨⟨h.1,h.2.1,fun i => ⟨hS.subset_atoms (h.2.2.1 i).1,hS.subset_atoms (h.2.2.1 i).2⟩,?_,?_⟩,h.2.2.1⟩
    · intro i
      exact (bondsBetween_closed_side M S hS (h.2.2.1 i).1 (h.2.2.1 i).2).symm.trans (h.2.2.2.1 i)
    · intro i
      obtain ⟨hu,hv,hd⟩ := h.2.2.2.2 i
      refine ⟨?_,?_,?_⟩
      · exact (bondsBetween_closed_side M S hS (h.2.2.1 i.castSucc).1 (h.2.2.1 i.succ).1).symm.trans hu
      · exact (bondsBetween_closed_side M S hS (h.2.2.1 i.castSucc).2 (h.2.2.1 i.succ).2).symm.trans hv
      · rw [← directed_closed_side_iff M S hS (h.2.2.1 i.castSucc).1,
          ← directed_closed_side_iff M S hS (h.2.2.1 i.succ).2]
        exact hd
  · rintro ⟨h,hm⟩
    refine ⟨h.1,h.2.1,hm,?_,?_⟩
    · intro i
      exact (bondsBetween_closed_side M S hS (hm i).1 (hm i).2).trans (h.2.2.2.1 i)
    · intro i
      obtain ⟨hu,hv,hd⟩ := h.2.2.2.2 i
      refine ⟨?_,?_,?_⟩
      · exact (bondsBetween_closed_side M S hS (hm i.castSucc).1 (hm i.succ).1).trans hu
      · exact (bondsBetween_closed_side M S hS (hm i.castSucc).2 (hm i.succ).2).trans hv
      · rw [directed_closed_side_iff M S hS (hm i.castSucc).1,
          directed_closed_side_iff M S hS (hm i.succ).2]
        exact hd

end WaveTurbulence.Mole.AppbAlgorithm
