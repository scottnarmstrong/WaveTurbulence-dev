/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamBondDegrees
public import WaveTurbulenceVineParam.VineParamRealizedDegrees
import Mathlib.Tactic

/-! # Directed endpoints and source degree constraints for actual vines

The bond enumeration is furnished by the multiplicity-preserving matching
with the pinned template. Directions are taken from the actual molecule,
not imposed on the undirected drawing.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Directed endpoints in the literal atom labels of a realized vine. -/
@[expose] def realizedEnds {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (e : Fin (X.expand R.k).bonds.length ≃ internalBonds M S) (j : Fin (X.expand R.k).bonds.length) : ℕ×ℕ :=
  (R.f (M.atom (e j).1),R.f (M.atom (M.mate (e j).1)))

/-- Equality to a template label means equality to its actual atom. -/
theorem label_eq_iff_atomAt {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b v : V} (R : VineRealization M X S a b)
    (hv : v ∈ S) (i : Fin (X.expand R.k).n) :
    R.f v=i.1 ↔ v=(R.atomAt i).1 := by
  constructor
  · intro h
    apply R.injOn hv (R.atomAt i).2
    exact h.trans (R.label_atomAt i).symm
  · intro h
    rw [h,R.label_atomAt]

/-- The directed source degree equations survive the exact bond matching. -/
theorem realizedEnds_degrees {M : Molecule V D} (hM : M.IsMolecule) {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) (hB : M.IsBlock S a b)
    (e : Fin (X.expand R.k).bonds.length ≃ internalBonds M S)
    (i : Fin (X.expand R.k).n) :
    ((univ : Finset (Fin (X.expand R.k).bonds.length)).filter
      fun j => (realizedEnds R e j).1=i.1).card=(if i.1<2 then 1 else 2) ∧
    ((univ : Finset (Fin (X.expand R.k).bonds.length)).filter
      fun j => (realizedEnds R e j).2=i.1).card=(if i.1<2 then 1 else 2) := by
  have hout : ((univ : Finset (Fin (X.expand R.k).bonds.length)).filter
      fun j => (realizedEnds R e j).1=i.1)=
      univ.filter (fun j => M.atom (e j).1=(R.atomAt i).1) := by
    ext j
    have hp := (mem_filter.mp (e j).2).2.2.1
    rw [mem_filter,mem_filter]
    dsimp only [realizedEnds]
    rw [label_eq_iff_atomAt R hp i]
  have hin : ((univ : Finset (Fin (X.expand R.k).bonds.length)).filter
      fun j => (realizedEnds R e j).2=i.1)=
      univ.filter (fun j => M.atom (M.mate (e j).1)=(R.atomAt i).1) := by
    ext j
    have hp := (mem_filter.mp (e j).2).2.2.2
    rw [mem_filter,mem_filter]
    dsimp only [realizedEnds]
    rw [label_eq_iff_atomAt R hp i]
  rw [hout,hin,tail_count,head_count]
  exact realization_directed_degrees M hM R hB i

/-- Both directed endpoint labels are actual atoms of the expanded template. -/
theorem realizedEnds_bounds {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (e : Fin (X.expand R.k).bonds.length ≃ internalBonds M S)
    (j : Fin (X.expand R.k).bonds.length) :
    (realizedEnds R e j).1<(X.expand R.k).n ∧
    (realizedEnds R e j).2<(X.expand R.k).n := by
  have hp := (mem_filter.mp (e j).2).2.2
  constructor
  · exact mem_range.mp (R.image_eq ▸ mem_image.mpr ⟨_,hp.1,rfl⟩)
  · exact mem_range.mp (R.image_eq ▸ mem_image.mpr ⟨_,hp.2,rfl⟩)

end WaveTurbulence.Vine.Param
