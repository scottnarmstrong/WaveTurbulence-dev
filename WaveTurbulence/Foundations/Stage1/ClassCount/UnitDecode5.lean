/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitDecode4
public import WaveTurbulence.Foundations.Spine.SourceVineObjects
import Mathlib.Tactic

/-!
# CLASSCOUNT: runs of a block around an ingredient are unique

(a) `SourceVine.Chain` is `Vine.Chain`; (b) a connected group meeting a sub-block `R ⊆ S` (one of whose joints is a
joint of `S` and the other is outside the group) lies inside `R` (`conn_subset_block`); (c) hence the run `L₀` of a
`SkelDecomp` equals the run `L` of `ingredient_runs` (`left_run_eq`, `right_run_eq`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.Vine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem chain_of_source {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : LGSpine.SourceVine.Chain M S a b n) : Chain M S a b n := by
  induction h with
  | single hv => exact Chain.single hv
  | append _ hT hi hne ih => exact Chain.append ih hT hi hne

/-- A group-connected set meeting a sub-block `R ⊆ S` lies in `R`, provided that no atom of the group is a joint
of `R` that is not a joint of `S`. -/
theorem conn_subset_block (M : Molecule V D) (hM : M.IsMolecule) {S R L : Finset V} {a b r1 r2 : V}
    (hSB : M.IsBlock S a b) (hRS : R ⊆ S) (hR : M.IsBlock R r1 r2)
    (hr1 : r1 = a ∨ r1 = b ∨ r1 ∉ L) (hr2 : r2 = a ∨ r2 = b ∨ r2 ∉ L)
    (hLc : M.GroupConnected L) (hLS : L ⊆ S) {v : V} (hvL : v ∈ L) (hvR : v ∈ R) : L ⊆ R := by
  classical
  have hclosed : ∀ u w : V, (∃ x : D, M.InGroup L x ∧ M.atom x = u ∧ M.atom (M.mate x) = w) →
      (u ∈ R ↔ w ∈ R) := by
    rintro u w ⟨x, hx, hxu, hxw⟩
    have hxS : M.InGroup S x := ⟨hLS hx.1, hLS hx.2⟩
    have hmx : M.InGroup S (M.mate x) := ⟨hLS hx.2, by rw [M.mate_mate]; exact hLS hx.1⟩
    have huL : u ∈ L := hxu ▸ hx.1
    have hwL : w ∈ L := hxw ▸ hx.2
    constructor
    · intro huR
      have hu1 : u = r1 → r1 = a ∨ r1 = b := fun h => by
        rcases hr1 with h' | h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
        · exact absurd (h ▸ huL) h'
      have hu2 : u = r2 → r2 = a ∨ r2 = b := fun h => by
        rcases hr2 with h' | h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
        · exact absurd (h ▸ huL) h'
      have := dart_in_block_of_ne M hM hR hSB hRS huR hu1 hu2 hxu hxS
      rw [← hxw]; exact this.2
    · intro hwR
      have hw1 : w = r1 → r1 = a ∨ r1 = b := fun h => by
        rcases hr1 with h' | h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
        · exact absurd (h ▸ hwL) h'
      have hw2 : w = r2 → r2 = a ∨ r2 = b := fun h => by
        rcases hr2 with h' | h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
        · exact absurd (h ▸ hwL) h'
      have := dart_in_block_of_ne M hM hR hSB hRS hwR hw1 hw2 (x := M.mate x) (by rw [← hxw]) hmx
      have h2 := this.2
      rw [M.mate_mate, hxu] at h2; exact h2
  intro z hz
  have := hLc v hvL z hz
  have key : ∀ p q : V, Relation.EqvGen (fun a b => ∃ x, M.InGroup L x ∧ M.atom x = a ∧ M.atom (M.mate x) = b) p q →
      (p ∈ R ↔ q ∈ R) := by
    intro p q h
    induction h with
    | rel a b hab => exact hclosed a b hab
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  exact (key v z this).mp hvR


theorem side_sub_left (N : Molecule V D) (hN : N.IsMolecule) {S A P P' Q' : Finset V} {a b x y : V}
    (hSB : N.IsBlock S a b) (hA : N.IsBlock A x y) (hPB : N.IsBlock P a x) (hPI : P ∩ A = {x})
    (hPS : P ⊆ S) (hS' : S = P' ∪ A ∪ Q') (hxP' : x ∈ P')
    (hQ' : Q' = ∅ ∨ (y ≠ b ∧ N.IsBlock Q' y b ∧ Q' ∩ A = {y})) : P ⊆ P' := by
  intro v hv
  have hvS : v ∈ P' ∪ A ∪ Q' := hS' ▸ hPS hv
  have hxy : x ≠ y := hA.2.2.2.1
  rcases Finset.mem_union.mp hvS with h | hvQ
  · rcases Finset.mem_union.mp h with h | hvA
    · exact h
    · have : v ∈ P ∩ A := Finset.mem_inter.mpr ⟨hv, hvA⟩
      rw [hPI, Finset.mem_singleton] at this
      exact this ▸ hxP'
  · rcases hQ' with rfl | ⟨hyb, hQB, hQI⟩
    · simp at hvQ
    · have hyP : y ∉ P := by
        intro hy
        have : y ∈ P ∩ A := Finset.mem_inter.mpr ⟨hy, hA.2.2.1⟩
        rw [hPI, Finset.mem_singleton] at this
        exact hxy this.symm
      have hQS : Q' ⊆ S := by rw [hS']; exact Finset.subset_union_right
      have hsub := conn_subset_block N hN hSB hQS hQB (Or.inr (Or.inr hyP)) (Or.inr (Or.inl rfl))
        hPB.2.2.2.2.2.2.2.2.2 hPS hv hvQ
      have hxQ : x ∈ Q' := hsub hPB.2.2.1
      have : x ∈ Q' ∩ A := Finset.mem_inter.mpr ⟨hxQ, hA.2.1⟩
      rw [hQI, Finset.mem_singleton] at this
      exact absurd this hxy


theorem side_sub_right (N : Molecule V D) (hN : N.IsMolecule) {S A P P' Q' : Finset V} {a b x y : V}
    (hSB : N.IsBlock S a b) (hA : N.IsBlock A x y) (hPB : N.IsBlock P y b) (hPI : P ∩ A = {y})
    (hPS : P ⊆ S) (hS' : S = Q' ∪ A ∪ P') (hyP' : y ∈ P')
    (hQ' : Q' = ∅ ∨ (x ≠ a ∧ N.IsBlock Q' a x ∧ Q' ∩ A = {x})) : P ⊆ P' := by
  intro v hv
  have hvS : v ∈ Q' ∪ A ∪ P' := hS' ▸ hPS hv
  have hxy : x ≠ y := hA.2.2.2.1
  rcases Finset.mem_union.mp hvS with h | hvP'
  · rcases Finset.mem_union.mp h with hvQ | hvA
    · rcases hQ' with rfl | ⟨hxa, hQB, hQI⟩
      · simp at hvQ
      · have hxP : x ∉ P := by
          intro hx
          have : x ∈ P ∩ A := Finset.mem_inter.mpr ⟨hx, hA.2.1⟩
          rw [hPI, Finset.mem_singleton] at this
          exact hxy this
        have hQS : Q' ⊆ S := by rw [hS']; exact Finset.subset_union_left.trans Finset.subset_union_left
        have hsub := conn_subset_block N hN hSB hQS hQB (Or.inl rfl) (Or.inr (Or.inr hxP))
          hPB.2.2.2.2.2.2.2.2.2 hPS hv hvQ
        have hyQ : y ∈ Q' := hsub hPB.2.1
        have : y ∈ Q' ∩ A := Finset.mem_inter.mpr ⟨hyQ, hA.2.2.1⟩
        rw [hQI, Finset.mem_singleton] at this
        exact absurd this.symm hxy
    · have : v ∈ P ∩ A := Finset.mem_inter.mpr ⟨hv, hvA⟩
      rw [hPI, Finset.mem_singleton] at this
      exact this ▸ hyP'
  · exact hvP'

/-- The left run of a decomposition around `A` is unique. -/
theorem left_run_eq (N : Molecule V D) (hN : N.IsMolecule) {S A L0 R0 L R : Finset V} {a b x y : V}
    (hSB : N.IsBlock S a b) (hA : N.IsBlock A x y)
    (hS0 : S = L0 ∪ A ∪ R0) (hL0 : L0 = ∅ ∧ x = a ∨ (x ≠ a ∧ N.IsBlock L0 a x ∧ L0 ∩ A = {x}))
    (hR0 : R0 = ∅ ∨ (y ≠ b ∧ N.IsBlock R0 y b ∧ R0 ∩ A = {y}))
    (hS1 : S = L ∪ A ∪ R) (hL : L = ∅ ∧ x = a ∨ (x ≠ a ∧ N.IsBlock L a x ∧ L ∩ A = {x}))
    (hR : R = ∅ ∨ (y ≠ b ∧ N.IsBlock R y b ∧ R ∩ A = {y})) : L0 = L := by
  rcases hL0 with ⟨h0, hxa⟩ | ⟨hxa, hB0, hI0⟩
  · rcases hL with ⟨h1, -⟩ | ⟨hxa', -, -⟩
    · rw [h0, h1]
    · exact absurd hxa hxa'
  · rcases hL with ⟨-, hxa'⟩ | ⟨-, hB, hI⟩
    · exact absurd hxa' hxa
    · apply Finset.Subset.antisymm
      · exact side_sub_left N hN hSB hA hB0 hI0 (by rw [hS0]; exact Finset.subset_union_left.trans Finset.subset_union_left)
          hS1 hB.2.2.1 hR
      · exact side_sub_left N hN hSB hA hB hI (by rw [hS1]; exact Finset.subset_union_left.trans Finset.subset_union_left)
          hS0 hB0.2.2.1 hR0

/-- The right run of a decomposition around `A` is unique. -/
theorem right_run_eq (N : Molecule V D) (hN : N.IsMolecule) {S A L0 R0 L R : Finset V} {a b x y : V}
    (hSB : N.IsBlock S a b) (hA : N.IsBlock A x y)
    (hS0 : S = L0 ∪ A ∪ R0) (hL0 : L0 = ∅ ∨ (x ≠ a ∧ N.IsBlock L0 a x ∧ L0 ∩ A = {x}))
    (hR0 : R0 = ∅ ∧ y = b ∨ (y ≠ b ∧ N.IsBlock R0 y b ∧ R0 ∩ A = {y}))
    (hS1 : S = L ∪ A ∪ R) (hL : L = ∅ ∨ (x ≠ a ∧ N.IsBlock L a x ∧ L ∩ A = {x}))
    (hR : R = ∅ ∧ y = b ∨ (y ≠ b ∧ N.IsBlock R y b ∧ R ∩ A = {y})) : R0 = R := by
  rcases hR0 with ⟨h0, hyb⟩ | ⟨hyb, hB0, hI0⟩
  · rcases hR with ⟨h1, -⟩ | ⟨hyb', -, -⟩
    · rw [h0, h1]
    · exact absurd hyb hyb'
  · rcases hR with ⟨-, hyb'⟩ | ⟨-, hB, hI⟩
    · exact absurd hyb' hyb
    · apply Finset.Subset.antisymm
      · exact side_sub_right N hN hSB hA hB0 hI0
          (by rw [hS0]; exact Finset.subset_union_right) (by rw [hS1]) hB.2.1 hL
      · exact side_sub_right N hN hSB hA hB hI
          (by rw [hS1]; exact Finset.subset_union_right) (by rw [hS0]) hB0.2.1 hL0


end WaveTurbulence.ClassCount
