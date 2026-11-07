/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.VrSlotCut
public import WaveTurbulence.Foundations.FinalCount.VrChain
public import WaveTurbulence.Foundations.FinalCount.AsmRho1
import Mathlib.Tactic

/-! # VINE-RHO (4): every inserted rung chain with `k ≥ 2` is a ladder

Glue: a realized slot of a vine gives a labelled full rung sequence, the inserted atoms are balanced (they have
full degree in the block), and the 2-cut of the slot forces the first net rail flow to vanish. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineRho
open WaveTurbulence WaveTurbulence.Vine Finset
set_option linter.unusedSectionVars false
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
theorem interior_balanced (M : Molecule V D) (hM : M.IsMolecule) {S : Finset V} {a b v : V}
    (hB : M.IsBlock S a b) (hv : v ∈ S) (hva : v ≠ a) (hvb : v ≠ b) :
    M.outdeg v = M.indeg v := by
  have hbal := block_balanced M hM hB v hv
  have hint := hB.2.2.2.2.2.2.2.2.1 v hv hva hvb
  have h1 := Mole.outIn_add_inIn M S v
  have h2 := outIn_le_outdeg M S v
  have h3 := inIn_le_indeg M S v
  have h4 := hM.1 v (hB.1 hv)
  omega

/-- The label data of a realized slot. -/
theorem slot_lab (M : Molecule V D) {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) (A : RealizedSlot R) :
    Lab M A.Q R.f ((A.pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n) := by
  have hzs : (A.s, A.k) ∈ X.template.slots.zip R.k := by
    rw [A.loc]; exact List.mem_append_right _ List.mem_cons_self
  have hep := template_slot_endpoints X A.s (List.of_mem_zip hzs).1
  have hmono : X.template.n ≤ (A.pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n := by
    rw [fold_insertRungs_atoms]; omega
  refine ⟨fun i h1 h2 => (A.labels i h1 h2).1, fun i h1 h2 => (A.labels i h1 h2).2, ?_⟩
  rw [A.ports.1, A.ports.2.1, A.ports.2.2.1, A.ports.2.2.2]
  omega

/-- Inserted atoms are balanced. -/
theorem slot_balanced (M : Molecule V D) (hM : M.IsMolecule) {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) (hB : M.IsBlock S a b) (A : RealizedSlot R) :
    ∀ i, 1 ≤ i → i ≤ A.k →
      M.outdeg (A.Q.u i) = M.indeg (A.Q.u i) ∧ M.outdeg (A.Q.v i) = M.indeg (A.Q.v i) := by
  have hl := slot_lab M R A
  have hj : R.f a < 2 ∧ R.f b < 2 := by
    have h := R.joints_eq
    have ha : R.f a ∈ ({R.f a, R.f b} : Finset ℕ) := by simp
    have hb : R.f b ∈ ({R.f a, R.f b} : Finset ℕ) := by simp
    rw [h] at ha hb
    simp only [mem_insert, mem_singleton] at ha hb
    omega
  have hT : 2 ≤ X.template.n := template_two_le X
  have hmono : X.template.n ≤ (A.pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n := by
    rw [fold_insertRungs_atoms]; omega
  intro i h1 h2
  have e1 := hl.u i h1 h2
  have e2 := hl.v i h1 h2
  constructor
  · exact interior_balanced M hM hB (A.mem i).1
      (fun h => by rw [h] at e1; omega) (fun h => by rw [h] at e1; omega)
  · exact interior_balanced M hM hB (A.mem i).2
      (fun h => by rw [h] at e2; omega) (fun h => by rw [h] at e2; omega)

/-- The 2-cut forces the net rail flow at the start of the chain to vanish. -/
theorem slot_start_flow (M : Molecule V D) (hM : M.IsMolecule) {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) (hB : M.IsBlock S a b) (A : RealizedSlot R) (hk : 1 ≤ A.k) :
    M.dartSign ((A.Q.upper 1 le_rfl hk).dart 2) + M.dartSign ((A.Q.lower 1 le_rfl hk).dart 2) = 0 := by
  obtain ⟨T, hTS, hu0, hv0, hu1, hv1, hcard⟩ := slot_cut M R A hk
  set U := A.Q.upper 1 le_rfl hk
  set L := A.Q.lower 1 le_rfl hk
  have hzs : (A.s, A.k) ∈ X.template.slots.zip R.k := by
    rw [A.loc]; exact List.mem_append_right _ List.mem_cons_self
  have hne := template_slot_ne X A.s (List.of_mem_zip hzs).1
  have aU : M.atom (M.mate (U.dart 2)) = A.Q.u 0 := by rw [U.neighbor_eq]; rfl
  have aL : M.atom (M.mate (L.dart 2)) = A.Q.v 0 := by rw [L.neighbor_eq]; rfl
  have mU : M.atom (U.dart 2) = A.Q.u 1 := U.atom_eq 2
  have mL : M.atom (L.dart 2) = A.Q.v 1 := L.atom_eq 2
  let xu : {z : D // M.InGroup S z} := ⟨M.mate (U.dart 2), by
    refine ⟨?_, ?_⟩
    · show M.atom (M.mate (U.dart 2)) ∈ S
      rw [aU]; exact (A.mem 0).1
    · show M.atom (M.mate (M.mate (U.dart 2))) ∈ S
      rw [M.mate_mate, mU]; exact (A.mem 1).1⟩
  let xv : {z : D // M.InGroup S z} := ⟨M.mate (L.dart 2), by
    refine ⟨?_, ?_⟩
    · show M.atom (M.mate (L.dart 2)) ∈ S
      rw [aL]; exact (A.mem 0).2
    · show M.atom (M.mate (M.mate (L.dart 2))) ∈ S
      rw [M.mate_mate, mL]; exact (A.mem 1).2⟩
  have hxu : xu ∈ boundary (Mole.induced M S) T := by
    refine mem_filter.2 ⟨mem_univ _, ?_, ?_⟩
    · show M.atom (M.mate (U.dart 2)) ∈ T
      rw [aU]; exact hu0
    · show M.atom (M.mate (M.mate (U.dart 2))) ∉ T
      rw [M.mate_mate, mU]; exact hu1
  have hxv : xv ∈ boundary (Mole.induced M S) T := by
    refine mem_filter.2 ⟨mem_univ _, ?_, ?_⟩
    · show M.atom (M.mate (L.dart 2)) ∈ T
      rw [aL]; exact hv0
    · show M.atom (M.mate (M.mate (L.dart 2))) ∉ T
      rw [M.mate_mate, mL]; exact hv1
  have hxne : xu ≠ xv := by
    intro h
    have h' : M.atom xu.1 = M.atom xv.1 := by rw [h]
    change M.atom (M.mate (U.dart 2)) = M.atom (M.mate (L.dart 2)) at h'
    rw [aU, aL] at h'
    have := congrArg R.f h'
    rw [A.ports.1, A.ports.2.1] at this
    exact hne this
  have hcut : boundary (Mole.induced M S) T = {xu, xv} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · rw [card_pair hxne]; exact hcard
  have hopp := block_two_cut_opposite M hM hB T hTS xu xv hxne hcut
  have s1 := Mole.dartSign_mate M (U.dart 2)
  have s2 := Mole.dartSign_mate M (L.dart 2)
  change M.out (M.mate (U.dart 2)) ≠ M.out (M.mate (L.dart 2)) at hopp
  have key : ∀ x y : D, M.out x ≠ M.out y → M.dartSign x + M.dartSign y = 0 := by
    intro x y h
    unfold Molecule.dartSign
    cases hx : M.out x <;> cases hy : M.out y
    · exact absurd (hx.trans hy.symm) h
    · norm_num
    · norm_num
    · exact absurd (hx.trans hy.symm) h
  have := key _ _ hopp
  linarith

/-- **Every inserted chain with `k ≥ 2` rungs is a ladder.**  Its atom set contains all the inserted atoms. -/
theorem slot_ladder (M : Molecule V D) (hM : M.IsMolecule) {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) (hB : M.IsBlock S a b) (A : RealizedSlot R) (hk : 2 ≤ A.k) :
    ∃ L : Finset V, M.IsLadderSet L ∧ ∀ i, 1 ≤ i → i ≤ A.k → A.Q.u i ∈ L ∧ A.Q.v i ∈ L := by
  have hl := slot_lab M R A
  have hbal := slot_balanced M hM R hB A
  have h0 := slot_start_flow M hM R hB A (by omega)
  have hz := flow_zero hM hl hbal (by omega) h0
  obtain ⟨m, hm⟩ : ∃ m, A.k = m + 1 := ⟨A.k - 1, by omega⟩
  -- transport to `k = m + 1`
  have key : ∀ (k : ℕ) (hkm : k = m + 1) (Q : FullRungSequence M k) (hl : Lab M Q R.f
      ((A.pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n))
      (hz : ∀ i (h1 : 1 ≤ i) (h2 : i ≤ k),
        M.dartSign ((Q.upper i h1 h2).dart 3) + M.dartSign ((Q.lower i h1 h2).dart 3) = 0),
      ∃ L : Finset V, M.IsLadderSet L ∧ ∀ i, 1 ≤ i → i ≤ k → Q.u i ∈ L ∧ Q.v i ∈ L := by
    intro k hkm Q hl hz
    subst hkm
    refine ⟨Molecule.ladderAtoms (fun j : Fin (m + 1) => Q.u (j.val + 1))
        (fun j : Fin (m + 1) => Q.v (j.val + 1)), ⟨m, _, _, chain_isLadder hM hl (by omega) hz, rfl⟩, ?_⟩
    intro i h1 h2
    constructor
    · exact (FinalCount.mem_ladderAtoms _ _ _).2 ⟨⟨i - 1, by omega⟩, Or.inl (by simp only; congr 1; omega)⟩
    · exact (FinalCount.mem_ladderAtoms _ _ _).2 ⟨⟨i - 1, by omega⟩, Or.inr (by simp only; congr 1; omega)⟩
  exact key A.k hm A.Q hl hz

end WaveTurbulence.VineRho
