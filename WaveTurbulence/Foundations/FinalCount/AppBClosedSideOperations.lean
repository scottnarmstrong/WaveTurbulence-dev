/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBClosedSide
public import WaveTurbulence.Foundations.FinalCount.AppBS33Topology
import Mathlib.Tactic

/-! # Closed component sides under deletion and internal reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- An actual residual component is closed under every retained bond. -/
theorem appb_residual_closedSide (M : Molecule V D) (Y : Finset V) (v : V) :
    AppbClosedSide (Degen.eraseAtoms M Y) (Degen.residualComponent M Y v) where
  subset_atoms := by
    intro u hu
    have hh := (Degen.mem_residualComponent M Y v u).mp hu
    exact mem_sdiff.mpr ⟨hh.1,hh.2.1⟩
  mate_mem := by
    intro x
    change M.atom x.val ∈ Degen.residualComponent M Y v ↔
      M.atom (M.mate x.val) ∈ Degen.residualComponent M Y v
    have forward : ∀ z : Degen.RetainedDart M Y,
        M.atom z.val ∈ Degen.residualComponent M Y v →
        M.atom (M.mate z.val) ∈ Degen.residualComponent M Y v := by
      intro z hz
      have hp := (Degen.mem_residualComponent M Y v _).mp hz
      apply (Degen.mem_residualComponent M Y v _).mpr
      exact ⟨M.atom_mem _,z.property.2,Relation.EqvGen.trans _ _ _ hp.2.2
        (Relation.EqvGen.rel _ _ ⟨z.property.1,z.property.2,z.val,rfl,rfl⟩)⟩
    refine ⟨forward x,?_⟩
    intro hx
    have hh := forward ((Degen.eraseAtoms M Y).mate x) hx
    simpa only [Degen.eraseAtoms,M.mate_mate] using hh

/-- Adding a bond entirely inside a closed side leaves that side closed. -/
theorem AppbClosedSide.addBond {M : Molecule V D} {S : Finset V}
    (h : AppbClosedSide M S) {a b : V} (ha : a ∈ S) (hb : b ∈ S) :
    AppbClosedSide (addBond M a b) S where
  subset_atoms := by
    intro u hu
    exact mem_insert_of_mem (mem_insert_of_mem (h.subset_atoms hu))
  mate_mem := by
    rintro (x|t)
    · exact h.mate_mem x
    · cases t
      · change (b ∈ S ↔ a ∈ S)
        exact iff_of_true hb ha
      · change (a ∈ S ↔ b ∈ S)
        exact iff_of_true ha hb

/-- The reinsertion prescribed by 3S3-3G stays entirely in the 35 side,
including when its actual direction is reversed. -/
theorem appb_s33_reinsert_closedSide (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33.pattern)
    (hg : AppbS33SplitTopology M r) (i : Fin AppbPatternKind.s33.pattern.edges.length) :
    AppbClosedSide (r.directedPostWithBond 3 5 i) (appbS33Side r) := by
  have h := appb_residual_closedSide M r.removedAtoms (r.vertex 3)
  have hs := appb_s33_side_labels_topology M r hg
  unfold AppbRealization.directedPostWithBond
  split_ifs
  · exact h.addBond hs.2.2.1 hs.2.2.2.2.1
  · exact h.addBond hs.2.2.2.2.1 hs.2.2.1

end WaveTurbulence.Mole
