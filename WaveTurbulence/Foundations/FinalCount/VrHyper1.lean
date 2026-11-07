/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.VrSlotDir
public import WaveTurbulence.Foundations.FinalCount.AsmRho1
import Mathlib.Tactic

/-! # VINE-RHO (6): hyper objects, part 1 (agreement with the adjoint)

For an HV/HVC `S` of `M` the vine structure lives in the adjoint `M' = eraseBond M e`.  `Agree M M' a b` says that `M` and `M'`
have the same atoms and the same bond multiplicities/directions at every pair whose first atom is not a joint.  The inserted
rung chains of a vine in `M'` avoid the joints, so they are ladders of `M` too (`slot_ladder_free`, `ladder_of_agree`). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineRho
open WaveTurbulence WaveTurbulence.Vine Finset
set_option linter.unusedSectionVars false
universe u1 u2 u3
variable {V : Type u1} [DecidableEq V] {D : Type u2} [Fintype D] [DecidableEq D] {D' : Type u3} [Fintype D'] [DecidableEq D']

/-- `M'` agrees with `M` away from the pair of joints `a, b` (first coordinate not a joint). -/
def Agree (M : Molecule V D) (M' : Molecule V D') (a b : V) : Prop :=
  M'.atoms = M.atoms ∧ ∀ x y, x ≠ a → x ≠ b →
    M'.bondsBetween x y = M.bondsBetween x y ∧ (M'.Directed x y ↔ M.Directed x y)

theorem Agree.refl (M : Molecule V D) (a b : V) : Agree M M a b := ⟨rfl, fun _ _ _ _ => ⟨rfl, Iff.rfl⟩⟩

theorem agree_eraseBond (M : Molecule V D) (e : D) {a b : V} (he : M.ends e = s(a, b)) :
    Agree M (Molecule.eraseBond M e) a b := by
  have hme : M.ends (M.mate e) = s(a, b) := by
    rw [← he]; unfold Molecule.ends; rw [M.mate_mate]; exact Sym2.eq_swap
  refine ⟨rfl, fun x y hxa hxb => ?_⟩
  have hne : s(x, y) ≠ s(a, b) := by
    intro h
    have : x ∈ s(a, b) := by rw [← h]; exact Sym2.mem_mk_left x y
    rcases Sym2.mem_iff.1 this with h | h <;> contradiction
  have hxe : M.atom e = a ∨ M.atom e = b := by
    have : M.atom e ∈ s(a, b) := by rw [← he]; exact Sym2.mem_mk_left _ _
    exact Sym2.mem_iff.1 this
  have hxe' : M.atom (M.mate e) = a ∨ M.atom (M.mate e) = b := by
    have : M.atom (M.mate e) ∈ s(a, b) := by rw [← hme]; exact Sym2.mem_mk_left _ _
    exact Sym2.mem_iff.1 this
  constructor
  · unfold Molecule.bondsBetween
    refine Finset.card_bij (fun z _ => z.1) ?_ ?_ ?_
    · intro z hz
      simp only [Molecule.bonds, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hz
    · intro z _ w _ h; exact Subtype.ext h
    · intro d hd
      simp only [Molecule.bonds, Finset.mem_filter, Finset.mem_univ, true_and] at hd
      have h1 : d ≠ e := by rintro rfl; exact hne (hd.2.symm.trans he)
      have h2 : d ≠ M.mate e := by rintro rfl; exact hne (hd.2.symm.trans hme)
      refine ⟨⟨d, h1, h2⟩, ?_, rfl⟩
      simp only [Molecule.bonds, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hd
  · constructor
    · rintro ⟨z, hz, h1, h2⟩
      exact ⟨z.1, hz, h1, h2⟩
    · rintro ⟨d, hd, h1, h2⟩
      have hd1 : d ≠ e := by rintro rfl; rcases hxe with h | h <;> [exact hxa (h1.symm.trans h); exact hxb (h1.symm.trans h)]
      have hd2 : d ≠ M.mate e := by
        rintro rfl; rcases hxe' with h | h <;> [exact hxa (h1.symm.trans h); exact hxb (h1.symm.trans h)]
      exact ⟨⟨d, hd1, hd2⟩, hd, h1, h2⟩

/-- Ladders of `M'` avoiding the joints are ladders of `M`. -/
theorem ladder_of_agree {M : Molecule V D} {M' : Molecule V D'} {a b : V} (hA : Agree M M' a b) {m : ℕ}
    {u w : Fin (m + 1) → V} (hL : M'.IsLadder u w) (hu : ∀ j, u j ≠ a ∧ u j ≠ b ∧ w j ≠ a ∧ w j ≠ b) :
    M.IsLadder u w := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hL
  refine ⟨h1, h2, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · rw [← hA.1]; exact h3 j
  · rw [← (hA.2 _ _ (hu j).1 (hu j).2.1).1]; exact h4 j
  · obtain ⟨c1, c2, c3⟩ := h5 j
    have e1 := hA.2 (u j.castSucc) (u j.succ) (hu _).1 (hu _).2.1
    have e2 := hA.2 (w j.castSucc) (w j.succ) (hu _).2.2.1 (hu _).2.2.2
    have e3 := hA.2 (u j.castSucc) (u j.succ) (hu _).1 (hu _).2.1
    have e4 := hA.2 (w j.succ) (w j.castSucc) (hu _).2.2.1 (hu _).2.2.2
    refine ⟨e1.1 ▸ c1, e2.1 ▸ c2, ?_⟩
    rw [← e3.2, ← e4.2]; exact c3

/-- **Every inserted chain with `k ≥ 2` rungs is a ladder avoiding the joints** (variant of `slot_ladder`). -/
theorem slot_ladder_free (M : Molecule V D) (hM : M.IsMolecule) {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) (hB : M.IsBlock S a b) (A : RealizedSlot R) (hk : 2 ≤ A.k) :
    ∃ (m : ℕ) (u w : Fin (m + 1) → V), M.IsLadder u w ∧
      (∀ i, 1 ≤ i → i ≤ A.k → A.Q.u i ∈ Molecule.ladderAtoms u w ∧ A.Q.v i ∈ Molecule.ladderAtoms u w) ∧
      (∀ j, u j ≠ a ∧ u j ≠ b ∧ w j ≠ a ∧ w j ≠ b) ∧ ∀ j, u j ∈ S ∧ w j ∈ S := by
  have hl := slot_lab M R A
  have hbal := slot_balanced M hM R hB A
  have h0 := slot_start_flow M hM R hB A (by omega)
  have hz := flow_zero hM hl hbal (by omega) h0
  obtain ⟨m, hm⟩ : ∃ m, A.k = m + 1 := ⟨A.k - 1, by omega⟩
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
  have key : ∀ (k : ℕ) (hkm : k = m + 1) (Q : FullRungSequence M k) (hmem : ∀ i, Q.u i ∈ S ∧ Q.v i ∈ S) (hl : Lab M Q R.f
      ((A.pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n))
      (hz : ∀ i (h1 : 1 ≤ i) (h2 : i ≤ k),
        M.dartSign ((Q.upper i h1 h2).dart 3) + M.dartSign ((Q.lower i h1 h2).dart 3) = 0),
      ∃ (m' : ℕ) (u w : Fin (m' + 1) → V), M.IsLadder u w ∧
      (∀ i, 1 ≤ i → i ≤ k → Q.u i ∈ Molecule.ladderAtoms u w ∧ Q.v i ∈ Molecule.ladderAtoms u w) ∧
      (∀ j, u j ≠ a ∧ u j ≠ b ∧ w j ≠ a ∧ w j ≠ b) ∧ ∀ j, u j ∈ S ∧ w j ∈ S := by
    intro k hkm Q hmem hl hz
    subst hkm
    refine ⟨m, (fun j : Fin (m + 1) => Q.u (j.val + 1)), (fun j : Fin (m + 1) => Q.v (j.val + 1)),
      chain_isLadder hM hl (by omega) hz, ?_, ?_⟩
    · intro i h1 h2
      constructor
      · exact (FinalCount.mem_ladderAtoms _ _ _).2 ⟨⟨i - 1, by omega⟩, Or.inl (by simp only; congr 1; omega)⟩
      · exact (FinalCount.mem_ladderAtoms _ _ _).2 ⟨⟨i - 1, by omega⟩, Or.inr (by simp only; congr 1; omega)⟩
    · refine ⟨fun j => ?_, fun j => ⟨(hmem _).1, (hmem _).2⟩⟩
      have e1 := hl.u (j.val + 1) (by omega) (by omega)
      have e2 := hl.v (j.val + 1) (by omega) (by omega)
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
      · simp only at h; rw [h] at e1; omega
      · simp only at h; rw [h] at e1; omega
      · simp only at h; rw [h] at e2; omega
      · simp only at h; rw [h] at e2; omega
  exact key A.k hm A.Q A.mem hl hz

end WaveTurbulence.VineRho
