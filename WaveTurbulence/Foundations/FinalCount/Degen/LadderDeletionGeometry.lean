/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.CircuitDeletion
public import WaveTurbulence.Foundations.FinalCount.Degen.SourceLadder
public import WaveTurbulence.Foundations.FinalCount.Degen.LadderRestriction
import Mathlib.Tactic

/-! # Local ladder geometry and actual circuit loss after atom deletion -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Actual darts at a whose other endpoint is b. -/
def neighborDarts (M : Molecule V D) (a b : V) : Finset D :=
  (M.dartsAt a).filter fun x => M.atom (M.mate x) = b

/-- Orient an outgoing representative at the specified incident atom. -/
def orientBondAt (M : Molecule V D) (a : V) (x : D) : D :=
  if M.atom x = a then x else M.mate x

omit [DecidableEq D] in
/-- Orientation at a vertex is injective among the outgoing representatives. -/
theorem orientBondAt_injOn_bonds (M : Molecule V D) (a : V) :
    Set.InjOn (orientBondAt M a) M.bonds := by
  intro x hx y hy he
  have hxout : M.out x = true := (mem_filter.mp hx).2
  have hyout : M.out y = true := (mem_filter.mp hy).2
  by_cases hxa : M.atom x = a <;> by_cases hya : M.atom y = a
  · simpa only [orientBondAt, hxa, hya, ite_true] using he
  · have hh := congrArg M.out he
    simp only [orientBondAt, hxa, hya, ite_true, ite_false, M.out_mate, hxout, hyout] at hh
    contradiction
  · have hh := congrArg M.out he
    simp only [orientBondAt, hxa, hya, ite_true, ite_false, M.out_mate, hxout, hyout] at hh
    contradiction
  · apply Mole.mate_injective M
    simpa only [orientBondAt, hxa, hya, ite_false] using he

omit [Fintype D] [DecidableEq D] in
/-- For distinct endpoints a crossing bond gives exactly one dart at a,
independent of its original orientation. -/
theorem orientBondAt_endpoints (M : Molecule V D) {a b : V} (hab : a ≠ b) {x : D}
    (hx : M.ends x = s(a,b)) :
    M.atom (orientBondAt M a x) = a ∧ M.atom (M.mate (orientBondAt M a x)) = b := by
  have he : M.atom x = a ∧ M.atom (M.mate x) = b ∨
      M.atom x = b ∧ M.atom (M.mate x) = a := Sym2.eq_iff.mp hx
  rcases he with ⟨ha,hb⟩ | ⟨hb,ha⟩
  · simp only [orientBondAt, ha, ite_true, hb, and_self]
  · simp only [orientBondAt, hb, hab.symm, ite_false, ha, M.mate_mate, and_self]

omit [DecidableEq D] in
/-- Exact neighbor-dart count for distinct atoms, preserving multiplicities. -/
theorem card_neighborDarts (M : Molecule V D) {a b : V} (hab : a ≠ b) :
    (neighborDarts M a b).card = M.bondsBetween a b := by
  classical
  symm
  unfold Molecule.bondsBetween
  apply card_bij (fun x _ => orientBondAt M a x)
  · intro x hx
    obtain ⟨hxout,hxend⟩ := mem_filter.mp hx
    have he := orientBondAt_endpoints M hab hxend
    simp only [neighborDarts, Molecule.dartsAt, mem_filter, mem_univ, true_and]
    exact he
  · intro x hx y hy he
    exact orientBondAt_injOn_bonds M a (mem_filter.mp hx).1 (mem_filter.mp hy).1 he
  · intro x hx
    have he : M.atom x = a ∧ M.atom (M.mate x) = b := by
      simpa only [neighborDarts, Molecule.dartsAt, mem_filter, mem_univ, true_and] using hx
    cases hout : M.out x
    · refine ⟨M.mate x, ?_, ?_⟩
      · apply mem_filter.mpr
        constructor
        · simp only [Molecule.bonds, mem_filter, mem_univ, true_and, M.out_mate, hout]
          rfl
        · change s(M.atom (M.mate x), M.atom (M.mate (M.mate x))) = s(a,b)
          rw [M.mate_mate, he.1, he.2]
          exact Sym2.eq_swap
      · have hne : M.atom (M.mate x) ≠ a := by rw [he.2]; exact hab.symm
        simp only [orientBondAt, hne, ite_false, M.mate_mate]
    · refine ⟨x, ?_, ?_⟩
      · apply mem_filter.mpr
        constructor
        · exact mem_filter.mpr ⟨mem_univ x, hout⟩
        · change s(M.atom x, M.atom (M.mate x)) = s(a,b)
          rw [he.1, he.2]
      · simp only [orientBondAt, he.1, ite_true]

/-- A positive bond multiplicity gives actual undirected adjacency. -/
theorem adj_of_bondsBetween_pos (M : Molecule V D) {a b : V} (hab : a ≠ b)
    (hpos : 0 < M.bondsBetween a b) : M.Adj a b := by
  have hn : (neighborDarts M a b).Nonempty := card_pos.mp (by simpa only [card_neighborDarts M hab] using hpos)
  obtain ⟨x,hx⟩ := hn
  have he : M.atom x = a ∧ M.atom (M.mate x) = b := by
    simpa only [neighborDarts, Molecule.dartsAt, mem_filter, mem_univ, true_and] using hx
  exact ⟨x,he⟩

omit [DecidableEq D] in
@[simp] theorem mem_neighborDarts (M : Molecule V D) (a b : V) (x : D) :
    x ∈ neighborDarts M a b ↔ M.atom x = a ∧ M.atom (M.mate x) = b := by
  simp only [neighborDarts, Molecule.dartsAt, mem_filter, mem_univ, true_and]

omit [DecidableEq D] in
theorem bondsBetween_comm (M : Molecule V D) (a b : V) : M.bondsBetween a b = M.bondsBetween b a := by
  change (M.bonds.filter fun x => M.ends x = s(a,b)).card = (M.bonds.filter fun x => M.ends x = s(b,a)).card
  rw [show s(a,b) = s(b,a) from Sym2.eq_swap]

/-- Three boundary darts in one new component save two relative to the
one-boundary-dart minimum for the other components. -/
theorem card_newComponents_add_two_le_of_large_boundary (M : Molecule V D) (Y : Finset V)
    (S : Finset V) (hS : S ∈ newComponents M Y) (hthree : 3 ≤ (boundaryDarts M S).card) :
    (newComponents M Y).card + 2 ≤ (boundaryDarts M Y).card := by
  classical
  let C := newComponents M Y
  have hothers : (C.erase S).card ≤ ∑ T ∈ C.erase S, (boundaryDarts M T).card := by
    calc
      _ = ∑ _T ∈ C.erase S, 1 := by simp only [sum_const, smul_eq_mul, mul_one]
      _ ≤ _ := by
        apply sum_le_sum
        intro T hT
        have hTC : T ∈ newComponents M Y := (mem_erase.mp hT).2
        exact card_pos.mpr (mem_filter.mp hTC).2
  have hcard : (C.erase S).card + 1 = C.card := card_erase_add_one hS
  have hsum := sum_erase_add C (fun T => (boundaryDarts M T).card) hS
  have hupper := sum_newComponents_boundary_card_le M Y
  change (∑ T ∈ C, (boundaryDarts M T).card) ≤ _ at hupper
  change C.card + 2 ≤ _
  omega

/-- Literal embedding of a consecutive interval of rung indices. -/
def ladderIntervalEmbedding (m a k : ℕ) (h : a + k ≤ m) : Fin (k + 1) ↪ Fin (m + 1) where
  toFun i := ⟨a + i.val, by have hi := i.isLt; omega⟩
  inj' := by
    intro i j he
    apply Fin.ext
    have hh := congrArg Fin.val he
    dsimp only at hh
    omega

omit [DecidableEq D] in
/-- Every consecutive rung interval of positive length is a selected
source ladder. End-to-end extra bonds do not affect the selected structure. -/
theorem sourceLadder_interval (M : Molecule V D) {m : ℕ} {u v : Fin (m + 1) → V}
    (hL : SourceLadder M u v) (a k : ℕ) (hak : a + k ≤ m) (hk : 1 ≤ k) :
    SourceLadder M (fun i => u (ladderIntervalEmbedding m a k hak i))
      (fun i => v (ladderIntervalEmbedding m a k hak i)) := by
  let E := ladderIntervalEmbedding m a k hak
  obtain ⟨hu,hv,hcross⟩ := Sum.elim_injective.mp hL.2.1
  refine ⟨hk, ?_, ?_, ?_, ?_⟩
  · exact Sum.elim_injective.mpr ⟨hu.comp E.injective, hv.comp E.injective, fun i j => hcross _ _⟩
  · intro i
    exact hL.2.2.1 (E i)
  · intro i
    exact hL.2.2.2.1 (E i)
  · intro i
    let t : Fin m := ⟨a + i.val, by have hi := i.isLt; omega⟩
    have hleft : E i.castSucc = t.castSucc := Fin.ext rfl
    have hright : E i.succ = t.succ := by
      apply Fin.ext
      change a + (i.val + 1) = (a + i.val) + 1
      omega
    change M.bondsBetween (u (E i.castSucc)) (u (E i.succ)) = 1 ∧
      M.bondsBetween (v (E i.castSucc)) (v (E i.succ)) = 1 ∧
      (M.Directed (u (E i.castSucc)) (u (E i.succ)) ↔ M.Directed (v (E i.succ)) (v (E i.castSucc)))
    rw [hleft, hright]
    exact hL.2.2.2.2 t

/-- Exact atom count of an injective two-rail rung sequence. -/
theorem ladderAtoms_card_of_injective {m : ℕ} {u v : Fin (m + 1) → V}
    (hinj : Function.Injective (Sum.elim u v)) :
    (Molecule.ladderAtoms u v).card = 2 * (m + 1) := by
  obtain ⟨hu,hv,hcross⟩ := Sum.elim_injective.mp hinj
  have hdis : Disjoint (univ.image u) (univ.image v) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    obtain ⟨j,_,he⟩ := mem_image.mp hy
    exact hcross i j he.symm
  unfold Molecule.ladderAtoms
  rw [card_union_of_disjoint hdis, card_image_of_injective _ hu, card_image_of_injective _ hv]
  simp only [card_univ, Fintype.card_fin]
  omega

end WaveTurbulence.Degen
