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

/-- Local graph criterion for loss of two circuits: two bonds to one
neighbor and one to a second neighbor which remain connected after removal.
No degree bound or source estimate is assumed in this geometric lemma. -/
theorem circuitRank_drop_of_neighbor_detour (M : Molecule V D)
    (hconn : ∀ u ∈ M.atoms, ∀ z ∈ M.atoms, M.SameComponent u z)
    {v a b : V} (hv : v ∈ M.atoms) (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hdouble : 2 ≤ M.bondsBetween v a) (hsingle : 1 ≤ M.bondsBetween v b)
    (hpath : Relation.EqvGen (ResidualAdj M {v}) a b) :
    (eraseAtoms M {v}).circuitRank ≤ M.circuitRank - 2 := by
  classical
  let A := neighborDarts M v a
  let B := neighborDarts M v b
  have hA : 2 ≤ A.card := by dsimp only [A]; rwa [card_neighborDarts M hva]
  have hB : 1 ≤ B.card := by dsimp only [B]; rwa [card_neighborDarts M hvb]
  have hdis : Disjoint A B := by
    apply disjoint_left.mpr
    intro x hx hy
    have hx' := (mem_neighborDarts M v a x).mp hx
    have hy' := (mem_neighborDarts M v b x).mp hy
    exact hab (hx'.2.symm.trans hy'.2)
  obtain ⟨xA,hxA⟩ := card_pos.mp (by omega : 0 < A.card)
  obtain ⟨xB,hxB⟩ := card_pos.mp (by omega : 0 < B.card)
  have hxA' := (mem_neighborDarts M v a xA).mp hxA
  have hxB' := (mem_neighborDarts M v b xB).mp hxB
  have haM : a ∈ M.atoms := hxA'.2 ▸ M.atom_mem (M.mate xA)
  have hbM : b ∈ M.atoms := hxB'.2 ▸ M.atom_mem (M.mate xB)
  let S := residualComponent M {v} a
  have haS : a ∈ S := (mem_residualComponent M {v} a a).mpr
    ⟨haM, by simpa only [mem_singleton] using hva.symm, Relation.EqvGen.refl a⟩
  have hbS : b ∈ S := (mem_residualComponent M {v} a b).mpr
    ⟨hbM, by simpa only [mem_singleton] using hvb.symm, hpath⟩
  have hvS : v ∉ S := by
    intro hh
    exact ((mem_residualComponent M {v} a v).mp hh).2.1 (mem_singleton_self v)
  have hsub : (A ∪ B).image M.mate ⊆ boundaryDarts M S := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    have hyv : M.atom y = v ∧ (M.atom (M.mate y) = a ∨ M.atom (M.mate y) = b) := by
      rcases mem_union.mp hy with hy | hy
      · have hh := (mem_neighborDarts M v a y).mp hy
        exact ⟨hh.1, Or.inl hh.2⟩
      · have hh := (mem_neighborDarts M v b y).mp hy
        exact ⟨hh.1, Or.inr hh.2⟩
    simp only [boundaryDarts, mem_filter, mem_univ, true_and, M.mate_mate, hyv.1]
    constructor
    · rcases hyv.2 with hya | hyb
      · exact hya.symm ▸ haS
      · exact hyb.symm ▸ hbS
    · exact hvS
  have hthree : 3 ≤ (boundaryDarts M S).card := by
    have hc := card_le_card hsub
    rw [card_image_of_injective _ (Mole.mate_injective M), card_union_of_disjoint hdis] at hc
    omega
  have hSC : S ∈ newComponents M {v} := by
    apply mem_filter.mpr
    constructor
    · exact mem_image.mpr ⟨a, mem_sdiff.mpr ⟨haM, by simpa only [mem_singleton] using hva.symm⟩, rfl⟩
    · exact card_pos.mp (by omega)
  have hc := card_newComponents_add_two_le_of_large_boundary M {v} S hSC hthree
  have hb := card_boundary_add_twice_self_eq_deg M v
  have hi := card_incident_add_self_eq_deg M v
  have hd := circuitRank_erase_singleton_sub M hconn hv
  omega

/-- A selected two-rung rectangle supplies the required surviving detour.
Additional bonds anywhere in the molecule do not invalidate this lemma. -/
theorem circuitRank_drop_of_rectangle (M : Molecule V D)
    (hconn : ∀ u ∈ M.atoms, ∀ z ∈ M.atoms, M.SameComponent u z)
    {x a b c : V} (hx : x ∈ M.atoms)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hdouble : 2 ≤ M.bondsBetween x a) (hopposite : 1 ≤ M.bondsBetween b c)
    (hrail : 1 ≤ M.bondsBetween x b) (hother : 1 ≤ M.bondsBetween a c) :
    (eraseAtoms M {x}).circuitRank ≤ M.circuitRank - 2 := by
  apply circuitRank_drop_of_neighbor_detour M hconn hx hxa hxb hab hdouble hrail
  have h1 : ResidualAdj M {x} a c :=
    ⟨by simpa only [mem_singleton] using hxa.symm,
      by simpa only [mem_singleton] using hxc.symm,
      adj_of_bondsBetween_pos M hac (by omega)⟩
  have h2 : ResidualAdj M {x} c b :=
    ⟨by simpa only [mem_singleton] using hxc.symm,
      by simpa only [mem_singleton] using hxb.symm,
      Mole.adj_symmetric M (adj_of_bondsBetween_pos M hbc (by omega))⟩
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ h1) (Relation.EqvGen.rel _ _ h2)

/-- Every atom of a selected rung rectangle loses two circuits. This
prefix lemma applies to both the corrected source ladder and the old draft. -/
theorem rectangle_pair_circuit_loss (M : Molecule V D)
    (hconn : ∀ u ∈ M.atoms, ∀ z ∈ M.atoms, M.SameComponent u z)
    {n : ℕ} (u v : Fin n → V) (hinj : Function.Injective (Sum.elim u v))
    (hmem : ∀ i, u i ∈ M.atoms ∧ v i ∈ M.atoms)
    {i k : Fin n} (hik : i ≠ k)
    (hr1 : M.bondsBetween (u i) (v i) = 2) (hr2 : M.bondsBetween (u k) (v k) = 2)
    (hu : M.bondsBetween (u i) (u k) = 1) (hv : M.bondsBetween (v i) (v k) = 1) :
    (eraseAtoms M {u i}).circuitRank ≤ M.circuitRank - 2 ∧
      (eraseAtoms M {v i}).circuitRank ≤ M.circuitRank - 2 := by
  have hcross (j l : Fin n) : u j ≠ v l := by
    intro he
    have hh : (Sum.inl j : Fin n ⊕ Fin n) = Sum.inr l := hinj he
    cases hh
  have huu : u i ≠ u k := fun he => hik (Sum.inl.inj (hinj he))
  have hvv : v i ≠ v k := fun he => hik (Sum.inr.inj (hinj he))
  constructor
  · exact circuitRank_drop_of_rectangle M hconn (hmem i).1 (hcross i i) huu (hcross i k)
      (hcross k i).symm hvv (hcross k k) (by omega) (by omega) (by omega) (by omega)
  · have hr1' : M.bondsBetween (v i) (u i) = 2 := by rw [bondsBetween_comm]; exact hr1
    have hr2' : M.bondsBetween (v k) (u k) = 2 := by rw [bondsBetween_comm]; exact hr2
    exact circuitRank_drop_of_rectangle M hconn (hmem i).2 (hcross i i).symm hvv (hcross k i).symm
      (hcross i k) huu (hcross k k).symm (by omega) (by omega) (by omega) (by omega)

/-- Every rung of a source ladder has an adjacent selected rung. Its
rectangle gives two circuits lost when either of its atoms is removed. -/
theorem sourceLadder_rung_circuit_loss (M : Molecule V D)
    (hconn : ∀ u ∈ M.atoms, ∀ z ∈ M.atoms, M.SameComponent u z)
    {m : ℕ} {u v : Fin (m + 1) → V} (hL : SourceLadder M u v) (j : Fin (m + 1)) :
    (eraseAtoms M {u j}).circuitRank ≤ M.circuitRank - 2 ∧
      (eraseAtoms M {v j}).circuitRank ≤ M.circuitRank - 2 := by
  have hm := hL.1
  have hrails := hL.2.2.2.2
  by_cases hj : j.val < m
  · let t : Fin m := ⟨j.val,hj⟩
    have he : t.castSucc = j := Fin.ext rfl
    have hne : j ≠ t.succ := by intro hh; have hh' := congrArg Fin.val hh; dsimp only [t] at hh'; simp only [Fin.val_succ] at hh'; omega
    have hu : M.bondsBetween (u j) (u t.succ) = 1 := by simpa only [he] using (hrails t).1
    have hv : M.bondsBetween (v j) (v t.succ) = 1 := by simpa only [he] using (hrails t).2.1
    exact rectangle_pair_circuit_loss M hconn u v hL.2.1 hL.2.2.1 hne
      (hL.2.2.2.1 j) (hL.2.2.2.1 t.succ) hu hv
  · let t : Fin m := ⟨m-1,by omega⟩
    have he : t.succ = j := by apply Fin.ext; dsimp only [t]; simp only [Fin.val_succ]; omega
    have hne : j ≠ t.castSucc := by intro hh; have hh' := congrArg Fin.val hh; dsimp only [t] at hh'; simp only [Fin.val_castSucc] at hh'; omega
    have hu : M.bondsBetween (u j) (u t.castSucc) = 1 := by
      rw [bondsBetween_comm, ← he]
      exact (hrails t).1
    have hv : M.bondsBetween (v j) (v t.castSucc) = 1 := by
      rw [bondsBetween_comm, ← he]
      exact (hrails t).2.1
    exact rectangle_pair_circuit_loss M hconn u v hL.2.1 hL.2.2.1 hne
      (hL.2.2.2.1 j) (hL.2.2.2.1 t.castSucc) hu hv

/-- Any actual atom contained in a selected source ladder loses at least
two circuits on deletion; extra bonds between ladder ends are allowed. -/
theorem circuitRank_erase_sourceLadder_atom_le_sub_two (M : Molecule V D)
    (hconn : ∀ u ∈ M.atoms, ∀ z ∈ M.atoms, M.SameComponent u z)
    {S : Finset V} (hL : SourceLadderSet M S) {z : V} (hz : z ∈ S) :
    (eraseAtoms M {z}).circuitRank ≤ M.circuitRank - 2 := by
  obtain ⟨m,u,v,hL,rfl⟩ := hL
  obtain hz | hz := mem_union.mp hz
  · obtain ⟨j,_,rfl⟩ := mem_image.mp hz
    exact (sourceLadder_rung_circuit_loss M hconn hL j).1
  · obtain ⟨j,_,rfl⟩ := mem_image.mp hz
    exact (sourceLadder_rung_circuit_loss M hconn hL j).2

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

/-- A rung interval not meeting rung j has no atom at that deleted rung. -/
theorem ladderIntervalAtoms_disjoint_rung {m : ℕ}
    {u v : Fin (m + 1) → V} (hinj : Function.Injective (Sum.elim u v))
    (a k : ℕ) (hak : a + k ≤ m) (j : Fin (m + 1)) (houtside : j.val < a ∨ a + k < j.val) :
    Disjoint (Molecule.ladderAtoms (fun i => u (ladderIntervalEmbedding m a k hak i))
      (fun i => v (ladderIntervalEmbedding m a k hak i))) {u j, v j} := by
  classical
  let E := ladderIntervalEmbedding m a k hak
  obtain ⟨hu,hv,hcross⟩ := Sum.elim_injective.mp hinj
  have hne (i : Fin (k + 1)) : E i ≠ j := by
    intro he
    have hh := congrArg Fin.val he
    change a + i.val = j.val at hh
    have hi := i.isLt
    omega
  apply disjoint_left.mpr
  intro x hx hxr
  have hxr' : x = u j ∨ x = v j := by simpa only [mem_insert, mem_singleton] using hxr
  rcases mem_union.mp hx with hx | hx
  · obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    rcases hxr' with he | he
    · exact hne i (hu he)
    · exact hcross _ _ he
  · obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    rcases hxr' with he | he
    · exact hcross _ _ he.symm
    · exact hne i (hv he)

/-- Removing one rung leaves two possible ladder intervals. Intervals of
fewer than two rungs contribute length zero, and at most two length units
are lost, independently of the original ladder length. -/
theorem ladder_split_length_loss_le_two {m j : ℕ} (hj : j ≤ m) :
    m ≤ (j - 1) + (m - j - 1) + 2 := by omega

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

/-- The draft's literal ladder length recovers the selected sequence length. -/
theorem ladderLength_eq_of_injective {m : ℕ} {u v : Fin (m + 1) → V}
    (hinj : Function.Injective (Sum.elim u v)) :
    Molecule.ladderLength (Molecule.ladderAtoms u v) = m := by
  unfold Molecule.ladderLength
  rw [ladderAtoms_card_of_injective hinj]
  omega

/-- Consecutive interval segments carry only atoms of the original ladder. -/
theorem ladderIntervalAtoms_subset {m : ℕ} (u v : Fin (m + 1) → V)
    (a k : ℕ) (hak : a + k ≤ m) :
    Molecule.ladderAtoms (fun i => u (ladderIntervalEmbedding m a k hak i))
      (fun i => v (ladderIntervalEmbedding m a k hak i)) ⊆ Molecule.ladderAtoms u v := by
  intro x hx
  obtain hx | hx := mem_union.mp hx
  · obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact mem_union.mpr (Or.inl (mem_image.mpr ⟨_,mem_univ _,rfl⟩))
  · obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact mem_union.mpr (Or.inr (mem_image.mpr ⟨_,mem_univ _,rfl⟩))

omit [DecidableEq V] in
/-- Length is monotone under inclusion of the actual atom sets. -/
theorem ladderLength_mono {S T : Finset V} (hST : S ⊆ T) :
    Molecule.ladderLength S ≤ Molecule.ladderLength T := by
  have hc := card_le_card hST
  unfold Molecule.ladderLength
  omega

/-- If both surviving segments lie in one maximal extension, that one
extension already pays the sum of the two segment lengths. -/
theorem ladderLength_two_disjoint_subsets_le {S T U : Finset V} {m n : ℕ}
    (hS : S.card = 2 * (m + 1)) (hT : T.card = 2 * (n + 1))
    (hdis : Disjoint S T) (hSU : S ⊆ U) (hTU : T ⊆ U) :
    m + n + 1 ≤ Molecule.ladderLength U := by
  have hc := card_le_card (union_subset hSU hTU)
  rw [card_union_of_disjoint hdis, hS, hT] at hc
  unfold Molecule.ladderLength
  omega

/-- The surviving consecutive interval is an actual ladder after deleting
one or both atoms of the missing rung. This is the segment construction
used by the normalized removal estimate. -/
theorem sourceLadder_interval_erase_rung (M : Molecule V D) {m : ℕ}
    {u v : Fin (m + 1) → V} (hL : SourceLadder M u v)
    (a k : ℕ) (hak : a + k ≤ m) (hk : 1 ≤ k) (j : Fin (m + 1))
    (houtside : j.val < a ∨ a + k < j.val) (Y : Finset V) (hY : Y ⊆ {u j,v j}) :
    SourceLadder (eraseAtoms M Y) (fun i => u (ladderIntervalEmbedding m a k hak i))
      (fun i => v (ladderIntervalEmbedding m a k hak i)) := by
  have hdis := (ladderIntervalAtoms_disjoint_rung hL.2.1 a k hak j houtside).mono_right hY
  have hnot : ∀ i : Fin (k + 1), u (ladderIntervalEmbedding m a k hak i) ∉ Y ∧
      v (ladderIntervalEmbedding m a k hak i) ∉ Y := by
    intro i
    constructor
    · intro hi
      apply (disjoint_left.mp hdis) _ hi
      exact mem_union.mpr (Or.inl (mem_image.mpr ⟨i,mem_univ _,rfl⟩))
    · intro hi
      apply (disjoint_left.mp hdis) _ hi
      exact mem_union.mpr (Or.inr (mem_image.mpr ⟨i,mem_univ _,rfl⟩))
  exact (sourceLadder_erase_iff M Y _ _ hnot).mpr (sourceLadder_interval M hL a k hak hk)

/-- Disjoint index intervals give disjoint actual rung atom sets. -/
theorem ladderIntervalAtoms_disjoint {m : ℕ} {u v : Fin (m + 1) → V}
    (hinj : Function.Injective (Sum.elim u v)) (a k b l : ℕ)
    (hak : a + k ≤ m) (hbl : b + l ≤ m) (hsep : a + k < b ∨ b + l < a) :
    Disjoint (Molecule.ladderAtoms (fun i => u (ladderIntervalEmbedding m a k hak i))
      (fun i => v (ladderIntervalEmbedding m a k hak i)))
      (Molecule.ladderAtoms (fun i => u (ladderIntervalEmbedding m b l hbl i))
      (fun i => v (ladderIntervalEmbedding m b l hbl i))) := by
  classical
  let E := ladderIntervalEmbedding m a k hak
  let F := ladderIntervalEmbedding m b l hbl
  obtain ⟨hu,hv,hcross⟩ := Sum.elim_injective.mp hinj
  have hne (i : Fin (k + 1)) (j : Fin (l + 1)) : E i ≠ F j := by
    intro he
    have hh := congrArg Fin.val he
    change a + i.val = b + j.val at hh
    have hi := i.isLt
    have hj := j.isLt
    omega
  apply disjoint_left.mpr
  intro x hx hy
  rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
  · obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    obtain ⟨j,_,he⟩ := mem_image.mp hy
    exact hne i j (hu he.symm)
  · obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    obtain ⟨j,_,he⟩ := mem_image.mp hy
    exact hcross _ _ he.symm
  · obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    obtain ⟨j,_,he⟩ := mem_image.mp hy
    exact hcross _ _ he
  · obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    obtain ⟨j,_,he⟩ := mem_image.mp hy
    exact hne i j (hv he.symm)

omit [DecidableEq D] in
private theorem sourceLadderSet_nonempty_geometry (M : Molecule V D) {S : Finset V}
    (hS : SourceLadderSet M S) : S.Nonempty := by
  obtain ⟨m,u,v,h,rfl⟩ := hS
  exact ⟨u 0,mem_union.mpr (Or.inl (mem_image.mpr ⟨0,mem_univ _,rfl⟩))⟩

/-- Removing an atom of a selected rung produces at most two genuine
positive-length surviving ladders. Their total length loses at most two;
no empty/dummy ladder is introduced in the finite family. -/
theorem sourceLadder_split_after_atom_delete (M : Molecule V D) {m : ℕ}
    {u v : Fin (m + 1) → V} (hL : SourceLadder M u v) (j : Fin (m + 1))
    (z : V) (hz : z = u j ∨ z = v j) :
    ∃ C : Finset (Finset V), C.card ≤ 2 ∧
      (∀ S ∈ C, SourceLadderSet (eraseAtoms M {z}) S ∧ S ⊆ Molecule.ladderAtoms u v) ∧
      (C : Set (Finset V)).PairwiseDisjoint id ∧
      m ≤ (∑ S ∈ C, Molecule.ladderLength S) + 2 := by
  classical
  let N := eraseAtoms M {z}
  let O := Molecule.ladderAtoms u v
  let Good (C : Finset (Finset V)) : Prop := C.card ≤ 2 ∧
    (∀ S ∈ C, SourceLadderSet N S ∧ S ⊆ O) ∧
    (C : Set (Finset V)).PairwiseDisjoint id ∧
    m ≤ (∑ S ∈ C, Molecule.ladderLength S) + 2
  change ∃ C, Good C
  have hsingle (S : Finset V) (hS : SourceLadderSet N S) (hSO : S ⊆ O)
      (hl : m ≤ Molecule.ladderLength S + 2) : ∃ C, Good C := by
    refine ⟨{S},?_,?_,?_,?_⟩
    · simp only [card_singleton]; omega
    · intro T hT
      have he : T = S := mem_singleton.mp hT
      subst T
      exact ⟨hS,hSO⟩
    · intro A hA B hB hAB
      have hAS : A = S := mem_singleton.mp hA
      have hBS : B = S := mem_singleton.mp hB
      exact False.elim (hAB (hAS.trans hBS.symm))
    · simpa only [sum_singleton] using hl
  have hpair (S T : Finset V) (hS : SourceLadderSet N S) (hT : SourceLadderSet N T)
      (hSO : S ⊆ O) (hTO : T ⊆ O) (hdis : Disjoint S T)
      (hl : m ≤ Molecule.ladderLength S + Molecule.ladderLength T + 2) : ∃ C, Good C := by
    have hST : S ≠ T := by
      intro he
      obtain ⟨x,hx⟩ := sourceLadderSet_nonempty_geometry N hS
      exact (disjoint_left.mp hdis) hx (he ▸ hx)
    refine ⟨{S,T},?_,?_,?_,?_⟩
    · simpa only [card_pair hST] using (le_rfl : (2 : ℕ) ≤ 2)
    · intro U hU
      have hu : U = S ∨ U = T := by simpa only [mem_insert, mem_singleton] using hU
      rcases hu with rfl | rfl
      · exact ⟨hS,hSO⟩
      · exact ⟨hT,hTO⟩
    · intro A hA B hB hAB
      change A ∈ ({S,T} : Finset (Finset V)) at hA
      change B ∈ ({S,T} : Finset (Finset V)) at hB
      have ha : A = S ∨ A = T := by simpa only [mem_insert, mem_singleton] using hA
      have hb : B = S ∨ B = T := by simpa only [mem_insert, mem_singleton] using hB
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact False.elim (hAB rfl)
      · exact hdis
      · exact hdis.symm
      · exact False.elim (hAB rfl)
    · simpa only [sum_pair hST] using hl
  have hY : ({z} : Finset V) ⊆ {u j,v j} := singleton_subset_iff.mpr (by simpa only [mem_insert, mem_singleton] using hz)
  let kl := j.val - 1
  let kr := m - j.val - 1
  have hleft_bound : 0 + kl ≤ m := by dsimp only [kl]; have hj := j.isLt; omega
  let Sl := Molecule.ladderAtoms (fun i => u (ladderIntervalEmbedding m 0 kl hleft_bound i))
    (fun i => v (ladderIntervalEmbedding m 0 kl hleft_bound i))
  have hSlO : Sl ⊆ O := ladderIntervalAtoms_subset u v 0 kl hleft_bound
  have hleft (hj : 2 ≤ j.val) : SourceLadderSet N Sl ∧ Molecule.ladderLength Sl = kl := by
    have hk : 1 ≤ kl := by dsimp only [kl]; omega
    have hout : j.val < 0 ∨ 0 + kl < j.val := by dsimp only [kl]; omega
    have hs := sourceLadder_interval_erase_rung M hL 0 kl hleft_bound hk j hout {z} hY
    exact ⟨⟨kl,_,_,hs,rfl⟩,ladderLength_eq_of_injective hs.2.1⟩
  have hright (hj : j.val + 2 ≤ m) : ∃ Sr : Finset V,
      SourceLadderSet N Sr ∧ Sr ⊆ O ∧ Molecule.ladderLength Sr = kr ∧ Disjoint Sl Sr := by
    have hbound : (j.val + 1) + kr ≤ m := by dsimp only [kr]; omega
    have hk : 1 ≤ kr := by dsimp only [kr]; omega
    let Sr := Molecule.ladderAtoms (fun i => u (ladderIntervalEmbedding m (j.val+1) kr hbound i))
      (fun i => v (ladderIntervalEmbedding m (j.val+1) kr hbound i))
    have hout : j.val < j.val + 1 ∨ j.val + 1 + kr < j.val := Or.inl (by omega)
    have hs := sourceLadder_interval_erase_rung M hL (j.val+1) kr hbound hk j hout {z} hY
    have hdis : Disjoint Sl Sr := ladderIntervalAtoms_disjoint hL.2.1 0 kl (j.val+1) kr
      hleft_bound hbound (Or.inl (by dsimp only [kl]; omega))
    exact ⟨Sr,⟨kr,_,_,hs,rfl⟩,ladderIntervalAtoms_subset u v _ _ hbound,
      ladderLength_eq_of_injective hs.2.1,hdis⟩
  by_cases hjleft : 2 ≤ j.val
  · obtain ⟨hSl,hSlLen⟩ := hleft hjleft
    by_cases hjright : j.val + 2 ≤ m
    · obtain ⟨Sr,hSr,hSrO,hSrLen,hdis⟩ := hright hjright
      apply hpair Sl Sr hSl hSr hSlO hSrO hdis
      rw [hSlLen,hSrLen]
      dsimp only [kl,kr]
      have hj := j.isLt
      omega
    · apply hsingle Sl hSl hSlO
      rw [hSlLen]
      dsimp only [kl]
      omega
  · by_cases hjright : j.val + 2 ≤ m
    · obtain ⟨Sr,hSr,hSrO,hSrLen,_hdis⟩ := hright hjright
      apply hsingle Sr hSr hSrO
      rw [hSrLen]
      dsimp only [kr]
      omega
    · refine ⟨∅,?_,?_,?_,?_⟩
      · simp only [card_empty]; omega
      · intro S hS
        change S ∈ (∅ : Finset (Finset V)) at hS
        simp only [notMem_empty] at hS
      · intro S hS
        change S ∈ (∅ : Finset (Finset V)) at hS
        simp only [notMem_empty] at hS
      · simp only [sum_empty]
        omega

/-- Atom-set version of the actual two-segment deletion construction. -/
theorem sourceLadderSet_split_after_atom_delete (M : Molecule V D) {S : Finset V}
    (hS : SourceLadderSet M S) {z : V} (hz : z ∈ S) :
    ∃ C : Finset (Finset V), C.card ≤ 2 ∧
      (∀ T ∈ C, SourceLadderSet (eraseAtoms M {z}) T ∧ T ⊆ S) ∧
      (C : Set (Finset V)).PairwiseDisjoint id ∧
      Molecule.ladderLength S ≤ (∑ T ∈ C, Molecule.ladderLength T) + 2 := by
  obtain ⟨m,u,v,hL,rfl⟩ := hS
  rw [ladderLength_eq_of_injective hL.2.1]
  obtain hz | hz := mem_union.mp hz
  · obtain ⟨j,_,rfl⟩ := mem_image.mp hz
    exact sourceLadder_split_after_atom_delete M hL j (u j) (Or.inl rfl)
  · obtain ⟨j,_,rfl⟩ := mem_image.mp hz
    exact sourceLadder_split_after_atom_delete M hL j (v j) (Or.inr rfl)

omit [DecidableEq D] in
/-- Every genuine selected ladder set has the exact source cardinal/length relation. -/
theorem sourceLadderSet_card_eq_length (M : Molecule V D) {S : Finset V} (hS : SourceLadderSet M S) :
    S.card = 2 * (Molecule.ladderLength S + 1) := by
  obtain ⟨m,u,v,hL,rfl⟩ := hS
  rw [ladderLength_eq_of_injective hL.2.1, ladderAtoms_card_of_injective hL.2.1]

omit [DecidableEq D] in
/-- Genuine ladder pieces have positive length; no zero-length pieces are
silently treated as ladders in the splitting construction. -/
theorem sourceLadderSet_length_pos (M : Molecule V D) {S : Finset V} (hS : SourceLadderSet M S) :
    1 ≤ Molecule.ladderLength S := by
  obtain ⟨m,u,v,hL,rfl⟩ := hS
  rw [ladderLength_eq_of_injective hL.2.1]
  exact hL.1

omit [DecidableEq D] in
/-- A disjoint family of genuine ladder segments inside one extension has
no greater total length than that extension. This handles coinciding
maximal extensions without splitting into separate collision cases. -/
theorem sum_ladderLength_le_of_disjoint_subsets (M : Molecule V D)
    (C : Finset (Finset V)) (T : Finset V)
    (hC : ∀ S ∈ C, SourceLadderSet M S) (hT : SourceLadderSet M T)
    (hdis : (C : Set (Finset V)).PairwiseDisjoint id) (hsub : ∀ S ∈ C, S ⊆ T) :
    (∑ S ∈ C, Molecule.ladderLength S) ≤ Molecule.ladderLength T := by
  classical
  by_cases hne : C.Nonempty
  · have hcpos : 1 ≤ C.card := card_pos.mpr hne
    have hU : C.biUnion id ⊆ T := by
      intro x hx
      obtain ⟨S,hS,hx⟩ := mem_biUnion.mp hx
      exact hsub S hS hx
    have hbound := card_le_card hU
    rw [card_biUnion hdis] at hbound
    have he : (∑ S ∈ C, S.card) = 2 * ((∑ S ∈ C, Molecule.ladderLength S) + C.card) := by
      calc
        _ = ∑ S ∈ C, 2 * (Molecule.ladderLength S + 1) :=
          sum_congr rfl (fun S hS => sourceLadderSet_card_eq_length M (hC S hS))
        _ = 2 * ∑ S ∈ C, (Molecule.ladderLength S + 1) := by rw [mul_sum]
        _ = _ := by rw [sum_add_distrib]; simp only [sum_const, smul_eq_mul, mul_one]
    change (∑ S ∈ C, S.card) ≤ T.card at hbound
    rw [he, sourceLadderSet_card_eq_length M hT] at hbound
    omega
  · rw [not_nonempty_iff_eq_empty.mp hne, sum_empty]
    exact Nat.zero_le _

end WaveTurbulence.Degen
