/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33BoundaryRegular
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33NoNewBridge
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33LadderCharge
import Mathlib.Tactic

/-! # Derived graph invariants of the source continuation test -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem d33_boundary_four_table {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (h3 : M.deg (r.vertex 3) = 4) (h4 : M.deg (r.vertex 4) = 4) :
    ∀ a ∈ AppbPatternKind.d33.pattern.vertices,
      a ∉ AppbPatternKind.d33.pattern.removed → M.deg (r.vertex a) = 4 := by
  intro a ha hka
  have hlabels : AppbPatternKind.d33.pattern.vertices \ AppbPatternKind.d33.pattern.removed = {3,4} := by decide
  have ha' : a = 3 ∨ a = 4 := by
    have hh := mem_sdiff.mpr ⟨ha,hka⟩
    rw [hlabels] at hh
    exact mem_insert.mp hh |>.imp_right mem_singleton.mp
  rcases ha' with rfl | rfl <;> assumption

theorem D33Continues.double_boundary {M : Molecule V D}
    {r : AppbRealization M AppbPatternKind.d33.pattern} (h : D33Continues r) :
    M.bondsBetween (r.vertex 3) (r.vertex 4) = 2 := by
  obtain ⟨t,ht,ho⟩ := h
  have hm := appb_d33_internal_multiplicity r.post t
  have hp : r.post.bondsBetween (r.vertex 3) (r.vertex 4) = 2 := by
    rcases ht with ⟨ht1,ht2⟩ | ⟨ht1,ht2⟩
    · simpa only [ht1,ht2] using hm
    · rw [bondsBetween_symm r.post (r.vertex 3) (r.vertex 4)]
      simpa only [ht1,ht2] using hm
  have hn3 := (mem_sdiff.mp (r.vertex_mem_post 3 (by decide) (by decide))).2
  have hn4 := (mem_sdiff.mp (r.vertex_mem_post 4 (by decide) (by decide))).2
  have he : r.post.bondsBetween (r.vertex 3) (r.vertex 4) = M.bondsBetween (r.vertex 3) (r.vertex 4) :=
    Degen.bondsBetween_erase_eq M r.removedAtoms hn3 hn4
  exact he.symm.trans hp

theorem HasD33ResidualCommon.double_boundary {M : Molecule V D}
    {r : AppbRealization M AppbPatternKind.d33.pattern} (h : HasD33ResidualCommon r) :
    M.bondsBetween (r.vertex 3) (r.vertex 4) = 2 := by
  obtain ⟨t,ht⟩ := h
  have hm := (t.bondsBetween_vertices_eq 1 2 (by decide) (by decide)).trans
    (show AppbPatternKind.d33same.pattern.multiplicity 1 2 = 2 by decide)
  have hp : r.post.bondsBetween (r.vertex 3) (r.vertex 4) = 2 := by
    rcases ht with ⟨ht1,ht2⟩ | ⟨ht1,ht2⟩
    · simpa only [ht1,ht2] using hm
    · rw [bondsBetween_symm r.post (r.vertex 3) (r.vertex 4)]
      simpa only [ht1,ht2] using hm
  have hn3 := (mem_sdiff.mp (r.vertex_mem_post 3 (by decide) (by decide))).2
  have hn4 := (mem_sdiff.mp (r.vertex_mem_post 4 (by decide) (by decide))).2
  have he : r.post.bondsBetween (r.vertex 3) (r.vertex 4) = M.bondsBetween (r.vertex 3) (r.vertex 4) :=
    Degen.bondsBetween_erase_eq M r.removedAtoms hn3 hn4
  exact he.symm.trans hp

/-- DH23 algorithm remark one, without an assumed post bridge predicate. -/
theorem D33Continues.no_new_bridge {M : Molecule V D}
    {r : AppbRealization M AppbPatternKind.d33.pattern} (h : D33Continues r)
    (hb : ∀ e : D,¬Degen.IsBridge M e) :
    ∀ e : Degen.RetainedDart M r.removedAtoms,¬Degen.IsBridge r.post e :=
  d33_no_new_bridge M r hb h.double_boundary

/-- The continuing rung's zero resource charge is derived from its actual
figure and old molecule data, rather than imposed as a trace annotation. -/
theorem D33Continues.zero_charge {M : Molecule V D}
    {r : AppbRealization M AppbPatternKind.d33.pattern} (h : D33Continues r)
    (hM : M.IsMolecule) (ho : AppbD33BoundaryOpposite M r) :
    ChargedStep (ofMolecule M) (ofMolecule r.post) 0 :=
  d33_zero_charge_of_double (ofMolecule M) hM r h.boundary_four.1 h.boundary_four.2 h.double_boundary ho

end WaveTurbulence.Mole.AppbAlgorithm
