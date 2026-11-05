/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeConnectedBlocks
import Mathlib.Tactic

/-!
# Actual two-component partitions and vertex-deletion conditions

DH23 Lemma 4.11(ii): after deleting an interior atom the group remains
connected, or splits into exactly two components containing the two joints.
The definition below records the actual connected pieces and excludes all
cross edges; it contains no assumed overlap classification.
-/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

/-- The two actual components, with each designated joint in its component. -/
@[expose] def TwoComponents (S : Finset V) (a b : V) : Prop :=
  ∃ U W : Finset V, U ∪ W = S ∧ Disjoint U W ∧ GroupConnected M U ∧ GroupConnected M W ∧
    a ∈ U ∧ b ∈ W ∧ ∀ u ∈ U, ∀ v ∈ W, ¬ M.Adj u v

/-- The vertex-deletion premise in DH23 Lemma 4.11, on the actual graph. -/
@[expose] def InteriorDeletionProperty (S : Finset V) (a b : V) : Prop :=
  ∀ v ∈ S, v ≠ a → v ≠ b → GroupConnected M (S.erase v) ∨ TwoComponents M (S.erase v) a b

omit [Fintype D] in
/-- No path within a partitioned group can cross an empty edge cut. -/
theorem partition_path_side {P Q S : Finset V} (hcover : P ∪ Q = S)
    (hno : ∀ p ∈ P, ∀ q ∈ Q, ¬ M.Adj p q)
    {u v : V} (hp : (induced M S).SameComponent u v) : u ∈ P ↔ v ∈ P := by
  have closed : ∀ {a b}, a ∈ P → (induced M S).Adj a b → b ∈ P := by
    intro a b ha hab
    have hh := (induced_adj_iff M S a b).mp hab
    have hbS := hh.2.2
    rw [← hcover] at hbS
    rcases Finset.mem_union.mp hbS with hbP | hbQ
    · exact hbP
    · exact (hno a ha b hbQ hh.1).elim
  induction hp with
  | rel a b hab => exact ⟨fun ha => closed ha hab,
      fun hb => closed hb (adj_symmetric (induced M S) hab)⟩
  | refl => exact Iff.rfl
  | symm a b hab ih => exact ih.symm
  | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc

omit [Fintype D] in
/-- A connected group cannot be split into two nonempty parts with no
cross edges, using the actual half-edge paths. -/
theorem not_connected_of_partition {P Q S : Finset V} (hcover : P ∪ Q = S)
    (hdis : Disjoint P Q) (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hno : ∀ p ∈ P, ∀ q ∈ Q, ¬ M.Adj p q) : ¬ GroupConnected M S := by
  intro hc
  obtain ⟨p,hp⟩ := hP
  obtain ⟨q,hq⟩ := hQ
  have hpS : p ∈ S := hcover ▸ Finset.mem_union_left Q hp
  have hqS : q ∈ S := hcover ▸ Finset.mem_union_right P hq
  have hqP := (partition_path_side M hcover hno (hc.2 p hpS q hqS)).mp hp
  exact Finset.disjoint_left.mp hdis hqP hq

omit [DecidableEq V] [Fintype D] in
/-- Paths lift along an actual inclusion of induced atomic groups. -/
theorem induced_path_mono {A B : Finset V} (hAB : A ⊆ B) {u v : V}
    (hp : (induced M A).SameComponent u v) : (induced M B).SameComponent u v := by
  induction hp with
  | rel a b hab =>
    obtain ⟨ha,haA,hbA⟩ := (induced_adj_iff M A a b).mp hab
    exact Relation.EqvGen.rel _ _ ((induced_adj_iff M B a b).mpr ⟨ha,hAB haA,hAB hbA⟩)
  | refl => exact Relation.EqvGen.refl _
  | symm a b hab ih => exact sameComponent_symm (induced M B) ih
  | trans a b c hab hbc ihab ihbc => exact sameComponent_trans (induced M B) ihab ihbc

omit [Fintype D] in
/-- Any connected subgroup lies on one side of an actual empty edge cut. -/
theorem connected_partition_side {P Q S U : Finset V} (hcover : P ∪ Q = S)
    (hno : ∀ p ∈ P, ∀ q ∈ Q, ¬ M.Adj p q)
    (hUS : U ⊆ S) (hc : GroupConnected M U) : U ⊆ P ∨ U ⊆ Q := by
  obtain ⟨u,hu⟩ := hc.1
  have huS := hUS hu
  rw [← hcover] at huS
  rcases Finset.mem_union.mp huS with huP | huQ
  · left
    intro v hv
    have hp := induced_path_mono M hUS (hc.2 u hu v hv)
    exact (partition_path_side M hcover hno hp).mp huP
  · right
    intro v hv
    have hp := induced_path_mono M hUS (hc.2 u hu v hv)
    have hno' : ∀ q ∈ Q, ∀ p ∈ P, ¬ M.Adj q p := by
      intro q hq p hp hqp
      exact hno p hp q hq (adj_symmetric M hqp)
    exact (partition_path_side M (by rw [Finset.union_comm,hcover]) hno' hp).mp huQ

omit [Fintype D] in
/-- An arbitrary nonempty edge-cut partition of exactly two components
must coincide with those two components, up to exchange. -/
theorem two_components_partition {P Q S : Finset V} {a b : V}
    (hcover : P ∪ Q = S) (hdis : Disjoint P Q) (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hno : ∀ p ∈ P, ∀ q ∈ Q, ¬ M.Adj p q) (ht : TwoComponents M S a b) :
    GroupConnected M P ∧ GroupConnected M Q ∧ ((a ∈ P ∧ b ∈ Q) ∨ (a ∈ Q ∧ b ∈ P)) := by
  obtain ⟨U,W,hUW,_hdUW,hcU,hcW,ha,hb,_hnUW⟩ := ht
  have hUS : U ⊆ S := fun u hu => hUW ▸ Finset.mem_union_left W hu
  have hWS : W ⊆ S := fun w hw => hUW ▸ Finset.mem_union_right U hw
  have hUPQ := connected_partition_side M hcover hno hUS hcU
  have hWPQ := connected_partition_side M hcover hno hWS hcW
  have hPsub : P ⊆ S := fun p hp => hcover ▸ Finset.mem_union_left Q hp
  have hQsub : Q ⊆ S := fun q hq => hcover ▸ Finset.mem_union_right P hq
  rcases hUPQ with hUP | hUQ <;> rcases hWPQ with hWP | hWQ
  · obtain ⟨q,hq⟩ := hQ
    have hqS := hQsub hq
    rw [← hUW] at hqS
    have hqP := (Finset.mem_union.mp hqS).elim (fun hh => hUP hh) (fun hh => hWP hh)
    exact (Finset.disjoint_left.mp hdis hqP hq).elim
  · have hPU : P ⊆ U := by
      intro p hp
      have hpS := hPsub hp
      rw [← hUW] at hpS
      rcases Finset.mem_union.mp hpS with hpU | hpW
      · exact hpU
      · exact (Finset.disjoint_left.mp hdis hp (hWQ hpW)).elim
    have hQW : Q ⊆ W := by
      intro q hq
      have hqS := hQsub hq
      rw [← hUW] at hqS
      rcases Finset.mem_union.mp hqS with hqU | hqW
      · exact (Finset.disjoint_left.mp hdis (hUP hqU) hq).elim
      · exact hqW
    have hPUeq := Finset.Subset.antisymm hPU hUP
    have hQWeq := Finset.Subset.antisymm hQW hWQ
    exact ⟨hPUeq.symm ▸ hcU,hQWeq.symm ▸ hcW,Or.inl ⟨hUP ha,hWQ hb⟩⟩
  · have hPW : P ⊆ W := by
      intro p hp
      have hpS := hPsub hp
      rw [← hUW] at hpS
      rcases Finset.mem_union.mp hpS with hpU | hpW
      · exact (Finset.disjoint_left.mp hdis hp (hUQ hpU)).elim
      · exact hpW
    have hQU : Q ⊆ U := by
      intro q hq
      have hqS := hQsub hq
      rw [← hUW] at hqS
      rcases Finset.mem_union.mp hqS with hqU | hqW
      · exact hqU
      · exact (Finset.disjoint_left.mp hdis (hWP hqW) hq).elim
    have hPWeq := Finset.Subset.antisymm hPW hWP
    have hQUeq := Finset.Subset.antisymm hQU hUQ
    exact ⟨hPWeq.symm ▸ hcW,hQUeq.symm ▸ hcU,Or.inr ⟨hUQ ha,hWP hb⟩⟩
  · obtain ⟨p,hp⟩ := hP
    have hpS := hPsub hp
    rw [← hUW] at hpS
    have hpQ := (Finset.mem_union.mp hpS).elim (fun hh => hUQ hh) (fun hh => hWQ hh)
    exact (Finset.disjoint_left.mp hdis hp hpQ).elim

end WaveTurbulence.Mole
