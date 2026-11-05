/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineObjects
public import WaveTurbulence.Foundations.Molecule.VineRealizationPaths
import Mathlib.Tactic

/-! # Connectivity of vine chains (TARGET defvine) -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Connectivity of an atomic group in its induced half-edge molecule. -/
@[expose] def GroupConnected (M : Molecule V D) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, (Mole.induced M S).SameComponent u v

omit [DecidableEq V] [Fintype D] in
/-- Paths in an induced group remain paths in a larger induced group. -/
theorem induced_path_mono (M : Molecule V D) {S T : Finset V} (h : S ⊆ T)
    {u v : V} (hp : (Mole.induced M S).SameComponent u v) :
    (Mole.induced M T).SameComponent u v := by
  induction hp with
  | rel a b hab =>
    obtain ⟨hadj,ha,hb⟩ := (Mole.induced_adj_iff M S a b).mp hab
    exact Relation.EqvGen.rel _ _ ((Mole.induced_adj_iff M T a b).mpr ⟨hadj,h ha,h hb⟩)
  | refl a => exact Relation.EqvGen.refl a
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

omit [Fintype D] in
/-- Two connected atomic groups sharing an atom have connected union. -/
theorem groupConnected_union (M : Molecule V D) {S T : Finset V} {b : V}
    (hS : GroupConnected M S) (hT : GroupConnected M T) (hbS : b ∈ S) (hbT : b ∈ T) :
    GroupConnected M (S ∪ T) := by
  intro u hu v hv
  have left (x : V) (hx : x ∈ S ∪ T) : (Mole.induced M (S ∪ T)).SameComponent x b := by
    rcases mem_union.mp hx with hx | hx
    · exact induced_path_mono M subset_union_left (hS x hx b hbS)
    · exact induced_path_mono M subset_union_right (hT x hx b hbT)
  exact Relation.EqvGen.trans _ _ _ (left u hu) (Relation.EqvGen.symm _ _ (left v hv))

/-- Both declared chain joints belong to its atom set. -/
theorem chain_joints_mem {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Chain M S a b n) : a ∈ S ∧ b ∈ S := by
  induction h with
  | single h => obtain ⟨X,hX⟩ := h; exact ⟨hX.1.2.1,hX.1.2.2.1⟩
  | append _ hT _ _ ih =>
    obtain ⟨X,hX⟩ := hT
    exact ⟨mem_union_left _ ih.1,mem_union_right _ hX.1.2.2.1⟩

/-- Actual ordered concatenation preserves connectivity. -/
theorem chain_connected {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Chain M S a b n) : GroupConnected M S := by
  induction h with
  | single h => obtain ⟨X,hX⟩ := h; exact isVine_connected hX
  | append hS hT _ _ ih =>
    obtain ⟨X,hX⟩ := hT
    exact groupConnected_union M ih (isVine_connected hX) (chain_joints_mem hS).2 hX.1.2.1

/-- TARGET defvine: every VC is connected. -/
theorem isVC_connected {M : Molecule V D} {S : Finset V} {a b : V}
    (h : IsVC M S a b) : GroupConnected M S := by
  obtain ⟨_hB,n,hn⟩ := h
  exact chain_connected hn

end WaveTurbulence.Vine
