/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBFiniteCounts
import Mathlib.Tactic

/-! # Actual component sides and their half-edge carriers -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

structure AppbClosedSide (M : Molecule V D) (S : Finset V) : Prop where
  subset_atoms : S ⊆ M.atoms
  mate_mem : ∀ x,M.atom x ∈ S ↔ M.atom (M.mate x) ∈ S

abbrev AppbSideDart (M : Molecule V D) (S : Finset V) := {x : D // M.atom x ∈ S}

def appbSideMolecule (M : Molecule V D) (S : Finset V) (h : AppbClosedSide M S) :
    Molecule V (AppbSideDart M S) where
  atoms := S
  atom := fun x => M.atom x.val
  mate := fun x => ⟨M.mate x.val,(h.mate_mem x.val).mp x.property⟩
  out := fun x => M.out x.val
  atom_mem := fun x => x.property
  mate_mate := fun x => Subtype.ext (M.mate_mate x.val)
  mate_ne := fun x hx => M.mate_ne x.val (congrArg Subtype.val hx)
  out_mate := fun x => M.out_mate x.val

theorem AppbClosedSide.complement {M : Molecule V D} {S : Finset V} (h : AppbClosedSide M S) :
    AppbClosedSide M (M.atoms \ S) where
  subset_atoms := sdiff_subset
  mate_mem := by
    intro x
    simp only [mem_sdiff,M.atom_mem,true_and]
    exact (h.mate_mem x).not

/-- Every incidence at an atom on a closed side is retained, exactly. -/
theorem appb_sum_dartsAt_side (M : Molecule V D) (S : Finset V) (h : AppbClosedSide M S)
    {A : Type*} [AddCommMonoid A] (f : D → A) {v : V} (hv : v ∈ S) :
    (∑ x ∈ (appbSideMolecule M S h).dartsAt v,f x.val) = ∑ x ∈ M.dartsAt v,f x := by
  apply sum_bij (fun x _ => x.val)
  · intro x hx
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩
  · intro x hx y hy he
    exact Subtype.ext he
  · intro x hx
    have ha : M.atom x = v := (mem_filter.mp hx).2
    exact ⟨⟨x,ha.symm ▸ hv⟩,mem_filter.mpr ⟨mem_univ _,ha⟩,rfl⟩
  · intro x hx
    rfl

def appbSideLabels {K : Type*} (M : Molecule V D) (S : Finset V) (κ : D → K) : AppbSideDart M S → K :=
  fun x => κ x.val

noncomputable def appbGlueLabels {K : Type*} (M : Molecule V D) (S : Finset V)
    (κ1 : AppbSideDart M S → K) (κ2 : AppbSideDart M (M.atoms \ S) → K) : D → K := by
  classical
  exact fun x => if hx : M.atom x ∈ S then κ1 ⟨x,hx⟩ else κ2 ⟨x,mem_sdiff.mpr ⟨M.atom_mem x,hx⟩⟩

theorem appbGlueLabels_left {K : Type*} (M : Molecule V D) (S : Finset V)
    (κ1 : AppbSideDart M S → K) (κ2 : AppbSideDart M (M.atoms \ S) → K) :
    appbSideLabels M S (appbGlueLabels M S κ1 κ2) = κ1 := by
  classical
  funext x
  simp only [appbSideLabels,appbGlueLabels,dif_pos x.property]

theorem appbGlueLabels_right {K : Type*} (M : Molecule V D) (S : Finset V)
    (κ1 : AppbSideDart M S → K) (κ2 : AppbSideDart M (M.atoms \ S) → K) :
    appbSideLabels M (M.atoms \ S) (appbGlueLabels M S κ1 κ2) = κ2 := by
  classical
  funext x
  simp only [appbSideLabels,appbGlueLabels,dif_neg (mem_sdiff.mp x.property).2]

theorem appbGlueLabels_injective {K : Type*} (M : Molecule V D) (S : Finset V) :
    Function.Injective (fun q : (AppbSideDart M S → K) × (AppbSideDart M (M.atoms \ S) → K) =>
      appbGlueLabels M S q.1 q.2) := by
  intro q q' he
  apply Prod.ext
  · have hh := congrArg (appbSideLabels M S) he
    simpa only [appbGlueLabels_left] using hh
  · have hh := congrArg (appbSideLabels M (M.atoms \ S)) he
    simpa only [appbGlueLabels_right] using hh

end WaveTurbulence.Mole
