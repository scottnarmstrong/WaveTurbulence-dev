/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.Prop104One
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.YExceptional
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.PinchFinal
import Mathlib.Tactic

/-! # Complete (Y) sequences on 4-regular pseudomolecules

* The ending of a complete sequence on a 4-regular `𝕄` is (Y1) case 3 or (Y2).
* A connected 4-regular pseudomolecule with a quadruple bond is `Q`.
* After a complete (Y2) sequence, the post molecule is 4-regular and connected, and its triple bonds are the other triple
  bonds of `𝕄` (or it is `Q`).
* After a (Y1) case 3 sequence, `𝕄 ∖ chain` is connected, has `E = 2V − 1`, and the common far end has degree two.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- On a 4-regular molecule a complete (Y) sequence ends in (Y1) case 3 or (Y2). -/
theorem YChain.complete_4reg {M : Molecule V D} (C : YChain M) (h4 : ∀ v ∈ M.atoms, M.deg v = 4)
    (hc : C.Complete) :
    Nonempty (Y1End3 C) ∨ ∃ E : Y2End C, M.bondsBetween (M.atom (M.mate E.x)) (M.atom (M.mate E.y)) ≠ 2 := by
  have ha := h4 _ (C.mem C.n le_rfl).1
  have hb := h4 _ (C.mem C.n le_rfl).2
  rcases hc with h6 | hE2 | h3 | h2
  · omega
  · obtain ⟨E⟩ := hE2; have := E.hdeg; omega
  · exact Or.inl h3
  · exact Or.inr h2

omit [DecidableEq D] in
/-- **A connected pseudomolecule (degrees `≤ 4`) with a quadruple bond is `Q`.** -/
theorem isQ_of_quadruple {M : Molecule V D} (hdeg : ∀ v ∈ M.atoms, M.deg v ≤ 4)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v) {p q : V} (hpq : p ≠ q)
    (h4 : 4 ≤ M.bondsBetween p q) : IsQ M := by
  classical
  have hp : p ∈ M.atoms := mem_atoms_of_bondsBetween_pos (a := q) (by rw [Degen.bondsBetween_comm]; omega)
  have hq : q ∈ M.atoms := mem_atoms_of_bondsBetween_pos (a := p) (by omega)
  have hsp := Degen.sum_neighbor_bonds_le_degree M p {q} (by simpa using hpq)
  have hsq := Degen.sum_neighbor_bonds_le_degree M q {p} (by simpa using hpq.symm)
  rw [sum_singleton] at hsp hsq
  have hdp := hdeg p hp
  have hdq := hdeg q hq
  rw [Degen.bondsBetween_comm] at hsq
  have h4' : M.bondsBetween p q = 4 := by omega
  -- every dart at `p` goes to `q`, and conversely
  have hall : ∀ z, M.atom z = p ∨ M.atom z = q → M.atom (M.mate z) = p ∨ M.atom (M.mate z) = q := by
    intro z hz
    rcases hz with hz | hz
    · right
      have hfull : Degen.neighborDarts M p q = M.dartsAt p := by
        refine eq_of_subset_of_card_le (fun w hw => (mem_filter.mp hw).1) ?_
        rw [Degen.card_neighborDarts M hpq, h4']; unfold Molecule.deg at hdp; omega
      have hzm : z ∈ M.dartsAt p := mem_filter.mpr ⟨mem_univ _, hz⟩
      rw [← hfull] at hzm
      exact ((Degen.mem_neighborDarts M p q z).mp hzm).2
    · left
      have h4'' : M.bondsBetween q p = 4 := by rw [Degen.bondsBetween_comm]; exact h4'
      have hfull : Degen.neighborDarts M q p = M.dartsAt q := by
        refine eq_of_subset_of_card_le (fun w hw => (mem_filter.mp hw).1) ?_
        rw [Degen.card_neighborDarts M hpq.symm, h4'']; unfold Molecule.deg at hdq; omega
      have hzm : z ∈ M.dartsAt q := mem_filter.mpr ⟨mem_univ _, hz⟩
      rw [← hfull] at hzm
      exact ((Degen.mem_neighborDarts M q p z).mp hzm).2
  have hclosed : ∀ z, M.atom z ∈ ({p, q} : Finset V) → M.atom (M.mate z) ∈ ({p, q} : Finset V) := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz ⊢
    exact hall z hz
  have hatoms : M.atoms = {p, q} := by
    have hsub : ({p, q} : Finset V) ⊆ M.atoms := by
      intro v hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hp
      · exact hq
    refine subset_antisymm (fun v hv => ?_) hsub
    exact (mem_iff_of_sameComponent_of_closed hclosed (hconn p hp v hv)).mp (by simp)
  have hsum := Mole.sum_degrees_eq_two_mul_bonds M
  rw [hatoms, sum_pair hpq] at hsum
  have hdp' : M.deg p = 4 := by omega
  have hdq' : M.deg q = 4 := by omega
  exact ⟨p, q, hpq, hatoms, h4', by omega⟩

namespace TwoExit
variable {M : Molecule V D} (T : TwoExit M)

/-- Bond counts of the post molecule. -/
theorem post_bondsBetween (p q : V) :
    T.post.bondsBetween p q = (if p ∈ T.Y ∨ q ∈ T.Y then 0 else M.bondsBetween p q) +
      (if s(T.d, T.c) = s(p, q) then 1 else 0) := by
  unfold post
  rw [addBond_bondsBetween]
  congr 1
  split_ifs with h
  · rcases h with h | h
    · exact bondsBetween_erase_of_mem M T.Y h
    · rw [Degen.bondsBetween_comm]; exact bondsBetween_erase_of_mem M T.Y h
  · push Not at h
    exact Degen.bondsBetween_erase_eq _ _ h.1 h.2

end TwoExit

/-- **Triple bonds after a complete (Y2) sequence** on a molecule with at most two triple bonds: the post molecule is
`Q`, or all its bond counts are `≤ 3` with at most one triple bond (one of `𝕄`'s, away from the chain). -/
theorem Y2End.post_triples {M : Molecule V D} {C : YChain M} (E : Y2End C)
    (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v) (h4 : ∀ v ∈ M.atoms, M.deg v = 4)
    (hle3 : ∀ p q, M.bondsBetween p q ≤ 3)
    (htri : ∀ p q r s t u, 3 ≤ M.bondsBetween p q → 3 ≤ M.bondsBetween r s → 3 ≤ M.bondsBetween t u →
      s(p, q) = s(r, s) ∨ s(p, q) = s(t, u) ∨ s(r, s) = s(t, u))
    (hcomp : M.bondsBetween (M.atom (M.mate E.x)) (M.atom (M.mate E.y)) ≠ 2) :
    IsQ (E.toTwoExit hcap).post ∨
      ((∀ p q, (E.toTwoExit hcap).post.bondsBetween p q ≤ 3) ∧
        (∀ p q r s, 3 ≤ (E.toTwoExit hcap).post.bondsBetween p q → 3 ≤ (E.toTwoExit hcap).post.bondsBetween r s →
          s(p, q) = s(r, s))) := by
  classical
  set T := E.toTwoExit hcap with hT
  have hTY : T.Y = C.set := E.toTwoExit_Y hcap
  have hcd := E.toTwoExit_cd hcap
  have hdc : s(T.d, T.c) = s(M.atom (M.mate E.x), M.atom (M.mate E.y)) := by
    rcases hcd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact Sym2.eq_swap
    · rw [h1, h2]
  have hcd2 : M.bondsBetween T.d T.c ≠ 2 := by
    have := congrArg (fun s => s) hdc
    rcases hcd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, Degen.bondsBetween_comm]; exact hcomp
    · rw [h1, h2]; exact hcomp
  have hpdeg : ∀ v ∈ T.post.atoms, T.post.deg v ≤ 4 := by
    intro v hv
    rw [T.post_atoms] at hv
    rw [T.post_deg (mem_sdiff.mp hv).2, h4 v (mem_sdiff.mp hv).1]
  -- the triple of the chain is inside `Y`
  have hchain3 : M.bondsBetween (C.a 0) (C.b 0) = 3 := C.triple
  by_cases hq : 3 ≤ M.bondsBetween T.d T.c
  · -- a quadruple bond: `Q`
    left
    have hne : T.d ≠ T.c := T.c_ne_d.symm
    have hb := T.post_bondsBetween T.d T.c
    rw [ite_of_not (by rintro (h | h) <;> [exact T.d_notMem h; exact T.c_notMem h]), ite_of_pos rfl] at hb
    exact isQ_of_quadruple hpdeg (T.post_connected hconn) hne (by rw [hb]; have := hle3 T.d T.c; omega)
  push Not at hq
  right
  have hb : ∀ p q, T.post.bondsBetween p q = (if p ∈ T.Y ∨ q ∈ T.Y then 0 else M.bondsBetween p q) +
      (if s(T.d, T.c) = s(p, q) then 1 else 0) := T.post_bondsBetween
  -- a pair with three bonds in the post molecule is a triple of `𝕄` away from `Y`
  have h3 : ∀ p q, 3 ≤ T.post.bondsBetween p q → p ∉ T.Y ∧ q ∉ T.Y ∧ M.bondsBetween p q = 3 := by
    intro p q h
    rw [hb] at h
    by_cases hY : p ∈ T.Y ∨ q ∈ T.Y
    · rw [ite_of_pos hY] at h; split_ifs at h <;> omega
    · rw [ite_of_not hY] at h
      push Not at hY
      by_cases hs : s(T.d, T.c) = s(p, q)
      · rw [ite_of_pos hs] at h
        have : M.bondsBetween p q = M.bondsBetween T.d T.c := by
          rcases Sym2.eq_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [← h1, ← h2]
          · rw [← h1, ← h2, Degen.bondsBetween_comm]
        omega
      · rw [ite_of_not hs] at h
        exact ⟨hY.1, hY.2, by have := hle3 p q; omega⟩
  refine ⟨fun p q => ?_, fun p q r s hpq hrs => ?_⟩
  · rw [hb]
    by_cases hY : p ∈ T.Y ∨ q ∈ T.Y
    · rw [ite_of_pos hY]; split_ifs <;> omega
    · rw [ite_of_not hY]
      by_cases hs : s(T.d, T.c) = s(p, q)
      · rw [ite_of_pos hs]
        have : M.bondsBetween p q = M.bondsBetween T.d T.c := by
          rcases Sym2.eq_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [← h1, ← h2]
          · rw [← h1, ← h2, Degen.bondsBetween_comm]
        have := hle3 T.d T.c
        omega
      · rw [ite_of_not hs, add_zero]; exact hle3 p q
  · obtain ⟨hp, hq', h1⟩ := h3 p q hpq
    obtain ⟨hr, hs', h2⟩ := h3 r s hrs
    have ha0 : C.a 0 ∈ T.Y := by rw [hTY]; exact C.a_mem (Nat.zero_le _)
    rcases htri p q r s (C.a 0) (C.b 0) (by omega) (by omega) (by omega) with h | h | h
    · exact h
    · exfalso
      rcases Sym2.eq_iff.mp h with ⟨h', _⟩ | ⟨_, h'⟩
      · exact hp (h' ▸ ha0)
      · exact hq' (h' ▸ ha0)
    · exfalso
      rcases Sym2.eq_iff.mp h with ⟨h', _⟩ | ⟨_, h'⟩
      · exact hr (h' ▸ ha0)
      · exact hs' (h' ▸ ha0)

end WaveTurbulence.MoleProp4
