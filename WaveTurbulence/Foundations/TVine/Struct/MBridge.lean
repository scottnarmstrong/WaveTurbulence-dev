/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.UBase
public import WaveTurbulence.Foundations.TVine.Struct.Statement
import Mathlib.Tactic

/-!
# Molecule ↔ U-layer bridges for the structure statements (packet L3)

Complements L1's `Core.Bridge` (B0) with what the statements of `Struct.Statement` use:

* `crossBonds_eq_eW`: the bonds between disjoint `A, B ⊆ S` are `eW (wG (groupGraph M S)) A B`;
* `adjIn_groupGraph_sub_iff`, `connIn_iff`: connectivity inside `A ⊆ S` (`ConnIn`) is `ReflTransGen (AdjIn …)`;
* `crossDarts_eq_pair`: two named crossing bonds that are the only ones give a cut of size 2.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core CutAlg

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- The bonds (outgoing darts) from `u` to `v` and from `v` to `u` are the bonds of the group with ends `s(u, v)`. -/
theorem groupGraph_mult_eq_two_cards {S : Finset V} {u v : V} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    (groupGraph M S).mult s(u, v) =
      (M.bonds.filter fun x => M.atom x = u ∧ M.atom (M.mate x) = v).card +
        (M.bonds.filter fun x => M.atom x = v ∧ M.atom (M.mate x) = u).card := by
  rw [groupGraph_mult_eq_card, ← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_filter, mem_groupDarts, Finset.mem_union, Molecule.bonds, Finset.mem_univ, true_and,
      Molecule.ends, Sym2.eq_iff]
    constructor
    · rintro ⟨⟨ho, -, -⟩, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · exact Or.inl ⟨ho, h1, h2⟩
      · exact Or.inr ⟨ho, h1, h2⟩
    · rintro (⟨ho, h1, h2⟩ | ⟨ho, h1, h2⟩)
      · exact ⟨⟨ho, h1 ▸ hu, h2 ▸ hv⟩, Or.inl ⟨h1, h2⟩⟩
      · exact ⟨⟨ho, h1 ▸ hv, h2 ▸ hu⟩, Or.inr ⟨h1, h2⟩⟩
  · rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact huv (h1.2.1.symm.trans h2.2.1)

private theorem card_eq_double_sum {A B : Finset V} (P : Finset D) (f g : D → V)
    (hP : ∀ y ∈ P, f y ∈ A ∧ g y ∈ B) :
    P.card = ∑ u ∈ A, ∑ w ∈ B, (P.filter fun y => f y = u ∧ g y = w).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := A) (fun y hy => (hP y hy).1)]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.card_eq_sum_card_fiberwise (f := g) (t := B)
    (fun y hy => (hP y (Finset.mem_filter.mp hy).1).2)]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.filter_filter]

/-- **The bonds between disjoint `A, B ⊆ S`** are counted by the weight of the group graph. -/
theorem crossBonds_eq_eW {S A B : Finset V} (hA : A ⊆ S) (hB : B ⊆ S) (hAB : Disjoint A B) :
    crossBonds M A B = eW (wG (groupGraph M S)) A B := by
  set P₁ := M.bonds.filter fun x => M.atom x ∈ A ∧ M.atom (M.mate x) ∈ B
  set P₂ := M.bonds.filter fun x => M.atom x ∈ B ∧ M.atom (M.mate x) ∈ A
  have hsplit : (M.bonds.filter fun x =>
      (M.atom x ∈ A ∧ M.atom (M.mate x) ∈ B) ∨ (M.atom x ∈ B ∧ M.atom (M.mate x) ∈ A)) = P₁ ∪ P₂ := by
    ext y; simp only [P₁, P₂, Finset.mem_union, Finset.mem_filter]; tauto
  have hdisj : Disjoint P₁ P₂ := by
    rw [Finset.disjoint_left]; intro y h1 h2
    exact Finset.disjoint_left.mp hAB (Finset.mem_filter.mp h1).2.1 (Finset.mem_filter.mp h2).2.1
  unfold crossBonds
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  rw [card_eq_double_sum P₁ M.atom (fun y => M.atom (M.mate y)) (fun y hy => (Finset.mem_filter.mp hy).2)]
  rw [card_eq_double_sum P₂ (fun y => M.atom (M.mate y)) M.atom (fun y hy => by
      have h := (Finset.mem_filter.mp hy).2; exact ⟨h.2, h.1⟩)]
  rw [← Finset.sum_add_distrib]
  unfold eW
  apply Finset.sum_congr rfl
  intro u hu
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  have huw : u ≠ w := fun h => Finset.disjoint_left.mp hAB hu (h ▸ hw)
  simp only [wG]
  rw [groupGraph_mult_eq_two_cards M (hA hu) (hB hw) huw, Finset.filter_filter, Finset.filter_filter]
  have e1 : ∀ y ∈ M.bonds, ((M.atom y ∈ A ∧ M.atom (M.mate y) ∈ B) ∧ M.atom y = u ∧ M.atom (M.mate y) = w) ↔
      (M.atom y = u ∧ M.atom (M.mate y) = w) :=
    fun y _ => ⟨fun h => h.2, fun h => ⟨⟨h.1 ▸ hu, h.2 ▸ hw⟩, h⟩⟩
  have e2 : ∀ y ∈ M.bonds, ((M.atom y ∈ B ∧ M.atom (M.mate y) ∈ A) ∧ M.atom (M.mate y) = u ∧ M.atom y = w) ↔
      (M.atom y = w ∧ M.atom (M.mate y) = u) :=
    fun y _ => ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨⟨h.1 ▸ hw, h.2 ▸ hu⟩, h.2, h.1⟩⟩
  rw [Finset.filter_congr e1, Finset.filter_congr e2]

/-- Adjacency inside a subset `A` of the group `S`. -/
theorem adjIn_groupGraph_sub_iff {S A : Finset V} (hA : A ⊆ S) {a b : V} :
    AdjIn (groupGraph M S) A a b ↔ ∃ x, M.InGroup A x ∧ M.atom x = a ∧ M.atom (M.mate x) = b := by
  rw [AdjIn, groupGraph_mult_eq_card, Finset.card_ne_zero]
  constructor
  · rintro ⟨ha, hb, y, hy⟩
    rw [Finset.mem_filter, mem_groupDarts] at hy; simp only [Molecule.ends, Sym2.eq_iff] at hy
    obtain ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hy
    · exact ⟨y, ⟨h1 ▸ ha, h2 ▸ hb⟩, h1, h2⟩
    · exact ⟨M.mate y, ⟨h2 ▸ ha, by rw [M.mate_mate]; exact h1 ▸ hb⟩, h2, by rw [M.mate_mate]; exact h1⟩
  · rintro ⟨x, hx, rfl, rfl⟩
    refine ⟨hx.1, hx.2, ?_⟩
    by_cases ho : M.out x = true
    · exact ⟨x, by simp [mem_groupDarts, ho, hA hx.1, hA hx.2, Molecule.ends]⟩
    · refine ⟨M.mate x, ?_⟩
      rw [Finset.mem_filter, mem_groupDarts]; simp only [M.out_mate, M.mate_mate, Molecule.ends]
      exact ⟨⟨by simpa using ho, hA hx.2, hA hx.1⟩, Sym2.eq_swap⟩

private theorem rtg_symm' {α : Type*} {r : α → α → Prop} (hr : ∀ a b, r a b → r b a) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .head (hr _ _ hbc) ih

private theorem eqvGen_iff_rtg' {α : Type*} {r : α → α → Prop} (hr : ∀ a b, r a b → r b a) {a b : α} :
    Relation.EqvGen r a b ↔ Relation.ReflTransGen r a b := by
  constructor
  · intro h
    induction h with
    | rel _ _ h => exact .single h
    | refl => exact .refl
    | symm _ _ _ ih => exact rtg_symm' hr ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    induction h with
    | refl => exact .refl _
    | tail _ h ih => exact .trans _ _ _ ih (.rel _ _ h)

/-- **`ConnIn` is U-level reachability** inside a subset `A` of the group `S`. -/
theorem connIn_iff {S A : Finset V} (hA : A ⊆ S) {u w : V} :
    ConnIn M A u w ↔ Relation.ReflTransGen (AdjIn (groupGraph M S) A) u w := by
  have hR : AdjIn (groupGraph M S) A =
      fun a b => ∃ x, M.InGroup A x ∧ M.atom x = a ∧ M.atom (M.mate x) = b := by
    funext a b; exact propext (adjIn_groupGraph_sub_iff M hA)
  have hs : ∀ a b, (∃ x, M.InGroup A x ∧ M.atom x = a ∧ M.atom (M.mate x) = b) →
      ∃ x, M.InGroup A x ∧ M.atom x = b ∧ M.atom (M.mate x) = a := by
    rintro a b ⟨x, hx, rfl, rfl⟩
    exact ⟨M.mate x, ⟨hx.2, by rw [M.mate_mate]; exact hx.1⟩, rfl, by rw [M.mate_mate]⟩
  unfold ConnIn
  rw [hR, eqvGen_iff_rtg' hs]

/-- Two crossing bonds that are the only crossing bonds give a cut of size `2`. -/
theorem cut_eq_two_of_pair {S X : Finset V} (hX : X ⊆ S) {e f : D} (he : e ∈ M.bonds) (hf : f ∈ M.bonds)
    (hef : e ≠ f) (hce : CrossesIn M S X e) (hcf : CrossesIn M S X f)
    (honly : ∀ g ∈ M.bonds, CrossesIn M S X g → g = e ∨ g = f) : cut (groupGraph M S) X = 2 := by
  rw [cut_groupGraph M hX]
  have hset : crossDarts M S X = {e, f} := by
    ext g
    simp only [crossDarts, Finset.mem_filter, mem_groupDarts, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨ho, h1, h2⟩, hc⟩
      exact honly g (by simp [Molecule.bonds, ho]) ⟨⟨h1, h2⟩, hc⟩
    · rintro (rfl | rfl)
      · have ho : M.out g = true := by simpa [Molecule.bonds] using he
        exact ⟨⟨ho, hce.1.1, hce.1.2⟩, hce.2⟩
      · have ho : M.out g = true := by simpa [Molecule.bonds] using hf
        exact ⟨⟨ho, hcf.1.1, hcf.1.2⟩, hcf.2⟩
  rw [hset, Finset.card_pair hef]

end WaveTurbulence.TVine.Struct
