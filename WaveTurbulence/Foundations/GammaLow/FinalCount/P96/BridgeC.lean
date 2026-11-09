/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.FinalCount.P96.BridgeT
import Mathlib.Tactic

/-! # Bridge, part 3: the closure of a case-(4) component is D11's closure (packet L6, `C4TBridge`)

For a whole component `S = M.atoms` (every dart is a dart of the atomic group `S`):
* `isBlock_atoms`: `S` is a block with joints `b, b'` (the two β-atoms of degree 2; FinalShape);
* `groupBonds_atoms_count`: D11's `groupBonds` counts are `bondsBetween`;
* `isClosure_closureTwo`: two β-chains (`σ = 0`): main's `closureTwo` is D11's closure;
* `isTVine_of_two`: with a T-route of the closure, `M.IsTVine M.atoms b b'` (M2 §4.8 (A2)). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.GammaLow.FinalCount
universe u v
open WaveTurbulence.FinalCountG8 WaveTurbulence.MoleProp4 WaveTurbulence.TVine

section general
variable {V : Type*} {D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem filter_inGroup_atoms (N : Molecule V D) (s : Finset D) :
    s.filter (fun x => N.InGroup N.atoms x) = s :=
  Finset.filter_true_of_mem fun x _ => inGroup_atoms N x

theorem outIn_atoms (N : Molecule V D) (v : V) : N.outIn N.atoms v = N.outdeg v := by
  unfold Molecule.outIn Molecule.outdeg
  congr 1
  exact Finset.filter_congr fun x _ => ⟨fun h => h.2, fun h => ⟨inGroup_atoms N x, h⟩⟩

theorem inIn_atoms (N : Molecule V D) (v : V) : N.inIn N.atoms v = N.indeg v := by
  unfold Molecule.inIn Molecule.indeg
  congr 1
  exact Finset.filter_congr fun x _ => ⟨fun h => h.2, fun h => ⟨inGroup_atoms N x, h⟩⟩

theorem degIn_atoms (N : Molecule V D) (v : V) : N.degIn N.atoms v = N.deg v := by
  unfold Molecule.degIn Molecule.deg
  rw [filter_inGroup_atoms]

theorem groupConnected_atoms (N : Molecule V D) (h : ∀ a ∈ N.atoms, ∀ b ∈ N.atoms, N.SameComponent a b) :
    N.GroupConnected N.atoms := by
  intro a ha c hc
  have h' := h a ha c hc
  clear ha hc
  induction h' with
  | rel x y hxy =>
    obtain ⟨z, h1, h2⟩ := hxy
    exact Relation.EqvGen.rel _ _ ⟨z, inGroup_atoms N z, h1, h2⟩
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem groupBonds_atoms_count (N : Molecule V D) (e : Sym2 V) :
    (N.groupBonds N.atoms).count e = (molGraph N).mult e := by
  unfold Molecule.groupBonds
  rw [Multiset.count_map]
  change (Multiset.filter (fun a => e = N.ends a)
      (Finset.univ.filter fun x => N.out x = true ∧ N.InGroup N.atoms x).val).card =
    (N.bonds.filter fun x => N.ends x = e).card
  rw [← Finset.filter_val, Finset.card_val]
  congr 1
  ext x
  simp only [Molecule.bonds, mem_filter, mem_univ, true_and]
  exact ⟨fun h => ⟨h.1.1, h.2.symm⟩, fun h => ⟨⟨h.1, inGroup_atoms N x⟩, h.2.symm⟩⟩

theorem dartsAt_eq_pair {N : Molecule V D} {b : V} {y₁ y₂ : D} (h1 : N.atom y₁ = b) (h2 : N.atom y₂ = b)
    (hall : ∀ x, N.atom x = b → x = y₁ ∨ x = y₂) : N.dartsAt b = {y₁, y₂} := by
  ext x
  simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  exact ⟨hall x, by rintro (rfl | rfl); exacts [h1, h2]⟩

theorem groupNbrs_eq_pair {N : Molecule V D} {b : V} {y₁ y₂ : D} (hne : y₁ ≠ y₂) (hd : N.dartsAt b = {y₁, y₂}) :
    N.groupNbrs N.atoms b = {N.atom (N.mate y₁), N.atom (N.mate y₂)} := by
  unfold Molecule.groupNbrs
  rw [filter_inGroup_atoms, hd, Finset.insert_val_of_notMem (by simpa using hne)]
  simp

theorem loopless_molGraph {N : Molecule V D} (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) :
    (molGraph N).Loopless := by
  intro a
  rw [molGraph_mult]
  refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun x _ he => ?_)
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hloop x (h1.trans h2.symm)
  · exact hloop x (h1.trans h2.symm)

/-- The whole component is a block with joints `b, b'`. -/
theorem isBlock_atoms {N : Molecule V D} {b b' : V} (hb : b ∈ N.atoms) (hb' : b' ∈ N.atoms) (hbb' : b ≠ b')
    (hdb : N.outdeg b = 1 ∧ N.indeg b = 1) (hdb' : N.outdeg b' = 1 ∧ N.indeg b' = 1)
    (hdeg4 : ∀ v ∈ N.atoms, v ≠ b → v ≠ b' → N.deg v = 4)
    (hconn : ∀ a ∈ N.atoms, ∀ c ∈ N.atoms, N.SameComponent a c) : N.IsBlock N.atoms b b' := by
  refine ⟨subset_refl _, hb, hb', hbb', ?_, ?_, ?_, ?_, fun w hw h1 h2 => ?_, groupConnected_atoms N hconn⟩
  · rw [outIn_atoms]; exact hdb.1
  · rw [inIn_atoms]; exact hdb.2
  · rw [outIn_atoms]; exact hdb'.1
  · rw [inIn_atoms]; exact hdb'.2
  · rw [degIn_atoms]; exact hdeg4 w hw h1 h2

end general

section two
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **Two β-chains: `closureTwo` is D11's closure (`σ = 0`).** -/
theorem isClosure_closureTwo {M : Molecule V D} {cls : V → Cls} {odd : Prop} (hS : FinalShape M cls odd)
    {b b' : V} {y₁ y₂ y₃ y₄ : D} (D4 : Case4TwoData M cls b b' y₁ y₂ y₃ y₄)
    (hreg : RegCore (closureTwo M b b' y₁ y₂ y₃ y₄)) :
    M.IsClosure M.atoms b b' (molGraph (closureTwo M b b' y₁ y₂ y₃ y₄)) := by
  classical
  have hy12 : y₁ ≠ y₂ := fun h => D4.hfar1 (by rw [h])
  have hy34 : y₃ ≠ y₄ := fun h => D4.hfar2 (by rw [h])
  have hyd : ∀ y ∈ ({y₁, y₂, y₃, y₄} : Finset D), M.atom (M.mate y) ≠ b ∧ M.atom (M.mate y) ≠ b' := fun y hy =>
    ⟨fun h => D4.hnb (h ▸ D4.hendsE y hy), fun h => D4.hnb' (h ▸ D4.hendsE y hy)⟩
  have hat : ∀ {K : Finset V} {p q : D}, crossDarts M K = {p, q} → M.atom p ∈ K ∧ M.atom q ∈ K := by
    intro K p q h
    exact ⟨(mem_crossDarts.mp (by rw [h]; simp)).1, (mem_crossDarts.mp (by rw [h]; simp)).1⟩
  have hat1 : M.atom y₁ = b := mem_singleton.mp (hat D4.hc1).1
  have hat2 : M.atom y₂ = b := mem_singleton.mp (hat D4.hc1).2
  have hat3 : M.atom y₃ = b' := mem_singleton.mp (hat D4.hc2).1
  have hat4 : M.atom y₄ = b' := mem_singleton.mp (hat D4.hc2).2
  have hall1 : ∀ x, M.atom x = b → x = y₁ ∨ x = y₂ := by
    intro x hx
    have : x ∈ crossDarts M {b} := mem_crossDarts.mpr ⟨by rw [hx]; exact mem_singleton_self _,
      fun h => hS.noLoop x (hx.trans (mem_singleton.mp h).symm)⟩
    rw [D4.hc1] at this; simpa using this
  have hall2 : ∀ x, M.atom x = b' → x = y₃ ∨ x = y₄ := by
    intro x hx
    have : x ∈ crossDarts M {b'} := mem_crossDarts.mpr ⟨by rw [hx]; exact mem_singleton_self _,
      fun h => hS.noLoop x (hx.trans (mem_singleton.mp h).symm)⟩
    rw [D4.hc2] at this; simpa using this
  have hm : ∀ y ∈ ({y₁, y₂, y₃, y₄} : Finset D), M.atom (M.mate y) ∈ (M.atoms \ {b}) \ {b'} := fun y hy =>
    mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨M.atom_mem _, by simpa using (hyd y hy).1⟩, by simpa using (hyd y hy).2⟩
  have hAt := atoms_closureTwo M b b' y₁ y₂ y₃ y₄ (hm y₁ (by simp)) (hm y₂ (by simp)) (hm y₃ (by simp))
    (hm y₄ (by simp))
  have hσ : M.sigma b b' = 0 := by
    by_contra h
    exact D4.hnadj (adj_of_bondsBetween_pos (Nat.pos_of_ne_zero h))
  refine ⟨by rw [hσ]; norm_num, ?_, loopless_molGraph hreg.loop, {s(M.atom (M.mate y₁), M.atom (M.mate y₂)), s(M.atom (M.mate y₃), M.atom (M.mate y₄))},
    Or.inl ⟨hσ, M.atom (M.mate y₁), M.atom (M.mate y₂), M.atom (M.mate y₃), M.atom (M.mate y₄), groupNbrs_eq_pair hy12 (dartsAt_eq_pair hat1 hat2 hall1),
      groupNbrs_eq_pair hy34 (dartsAt_eq_pair hat3 hat4 hall2), rfl⟩, fun e => ?_⟩
  · show (closureTwo M b b' y₁ y₂ y₃ y₄).atoms = _
    rw [hAt, sdiff_singleton_eq_erase, sdiff_singleton_eq_erase]
  · induction e using Sym2.ind with
    | _ p q =>
    rw [Multiset.count_filter, groupBonds_atoms_count, molGraph_mult, molGraph_mult]
    have hcnt : ({s(M.atom (M.mate y₁), M.atom (M.mate y₂)), s(M.atom (M.mate y₃), M.atom (M.mate y₄))} : Multiset (Sym2 V)).count s(p, q) =
        (if s(p, q) = s(M.atom (M.mate y₃), M.atom (M.mate y₄)) then 1 else 0) + (if s(p, q) = s(M.atom (M.mate y₁), M.atom (M.mate y₂)) then 1 else 0) := by
      rw [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
    rw [hcnt]
    have hf : ∀ y ∈ ({y₁, y₂, y₃, y₄} : Finset D), ∀ x, x = M.atom (M.mate y) → x ≠ b ∧ x ≠ b' :=
      fun y hy x hx => hx ▸ hyd y hy
    by_cases hpq : (p = b ∨ p = b') ∨ (q = b ∨ q = b')
    · have h0 : (closureTwo M b b' y₁ y₂ y₃ y₄).bondsBetween p q = 0 := by
        by_contra h
        have := bb_pos_mem (Nat.pos_of_ne_zero h)
        rw [hAt] at this
        rcases hpq with (rfl | rfl) | (rfl | rfl) <;> simp at this
      have hnot : ¬ (b ∉ s(p, q) ∧ b' ∉ s(p, q)) := by
        rintro ⟨h1, h2⟩
        rcases hpq with (rfl | rfl) | (rfl | rfl)
        · exact h1 (Sym2.mem_mk_left _ _)
        · exact h2 (Sym2.mem_mk_left _ _)
        · exact h1 (Sym2.mem_mk_right _ _)
        · exact h2 (Sym2.mem_mk_right _ _)
      rw [h0, if_neg hnot]
      have n1 : ¬ s(p, q) = s(M.atom (M.mate y₃), M.atom (M.mate y₄)) := by
        intro h
        rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases hpq with (h | h) | (h | h) <;>
          first
          | exact (hf y₃ (by simp) _ rfl).1 h | exact (hf y₃ (by simp) _ rfl).2 h
          | exact (hf y₄ (by simp) _ rfl).1 h | exact (hf y₄ (by simp) _ rfl).2 h
      have n2 : ¬ s(p, q) = s(M.atom (M.mate y₁), M.atom (M.mate y₂)) := by
        intro h
        rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases hpq with (h | h) | (h | h) <;>
          first
          | exact (hf y₁ (by simp) _ rfl).1 h | exact (hf y₁ (by simp) _ rfl).2 h
          | exact (hf y₂ (by simp) _ rfl).1 h | exact (hf y₂ (by simp) _ rfl).2 h
      rw [if_neg n1, if_neg n2]
    · push Not at hpq
      obtain ⟨⟨hp, hp'⟩, hq, hq'⟩ := hpq
      have hin : b ∉ s(p, q) ∧ b' ∉ s(p, q) := by
        refine ⟨fun h => ?_, fun h => ?_⟩ <;> rcases Sym2.mem_iff.mp h with h | h
        exacts [hp h.symm, hq h.symm, hp' h.symm, hq' h.symm]
      rw [bb_closureTwo M b b' y₁ y₂ y₃ y₄ hp hp' hq hq', if_pos hin]
      have e1 : (if s(M.atom (M.mate y₃), M.atom (M.mate y₄)) = s(p, q) then 1 else 0) = (if s(p, q) = s(M.atom (M.mate y₃), M.atom (M.mate y₄)) then 1 else 0) := by
        by_cases h : s(p, q) = s(M.atom (M.mate y₃), M.atom (M.mate y₄))
        · rw [if_pos h.symm, if_pos h]
        · rw [if_neg (fun h' => h h'.symm), if_neg h]
      have e2 : (if s(M.atom (M.mate y₁), M.atom (M.mate y₂)) = s(p, q) then 1 else 0) = (if s(p, q) = s(M.atom (M.mate y₁), M.atom (M.mate y₂)) then 1 else 0) := by
        by_cases h : s(p, q) = s(M.atom (M.mate y₁), M.atom (M.mate y₂))
        · rw [if_pos h.symm, if_pos h]
        · rw [if_neg (fun h' => h h'.symm), if_neg h]
      rw [e1, e2]
      ring

/-- **Two β-chains with a T-route: the component is a T-vine.** -/
theorem isTVine_of_two {M : Molecule V D} {cls : V → Cls} {odd : Prop} (hS : FinalShape M cls odd)
    {b b' : V} {y₁ y₂ y₃ y₄ : D} (D4 : Case4TwoData M cls b b' y₁ y₂ y₃ y₄)
    (hreg : RegCore (closureTwo M b b' y₁ y₂ y₃ y₄)) {k : ℕ} (hroute : YRouteT k (closureTwo M b b' y₁ y₂ y₃ y₄)) :
    M.IsTVine M.atoms b b' := by
  obtain ⟨G', hpath, htri⟩ := yrouteT_graph hroute hreg
  exact ⟨isBlock_atoms D4.hb D4.hb' D4.hbb' (hS.dir2 b D4.hb D4.hdeg2) (hS.dir2 b' D4.hb' D4.hdeg2') D4.hdeg4 hS.conn,
    fun u _ w _ _ => hS.noTriple u w, molGraph _, G', isClosure_closureTwo hS D4 hreg, hpath, htri⟩

end two

section one
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem dartsAt_eq_of_pair {N : Molecule V D} {v : V} {e w : D} (he : N.atom e = v) (hw : N.atom w = v) (hew : e ≠ w)
    (hdeg : N.deg v = 2) : N.dartsAt v = {e, w} := by
  have hsub : ({e, w} : Finset D) ⊆ N.dartsAt v := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and]
    rcases hx with rfl | rfl
    exacts [he, hw]
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [card_pair hew]; exact hdeg.le

/-- One β-chain `u → b → b' → v`, with the exit `e` at `b` and `e'` at `b'`: `closureOne` is D11's closure (`σ = 1`). -/
theorem isClosure_closureOne_core {M : Molecule V D} {cls : V → Cls} {b b' : V} {x₁ x₂ y y' : D}
    (D1 : Case4OneData M cls b b' x₁ x₂ y y') (hreg : RegCore (closureOne M b b' x₁ x₂)) {e e' w : D}
    (he : M.atom e = b) (he' : M.atom e' = b') (hw1 : M.atom w = b) (hw2 : M.atom (M.mate w) = b')
    (hfe : M.atom (M.mate e) ∉ ({b, b'} : Finset V)) (hfe' : M.atom (M.mate e') ∉ ({b, b'} : Finset V))
    (hsym : s(M.atom (M.mate e), M.atom (M.mate e')) = s(M.atom (M.mate x₁), M.atom (M.mate x₂)))
    (hfx1 : M.atom (M.mate x₁) ∉ ({b, b'} : Finset V)) (hfx2 : M.atom (M.mate x₂) ∉ ({b, b'} : Finset V)) :
    M.IsClosure M.atoms b b' (molGraph (closureOne M b b' x₁ x₂)) := by
  classical
  have hew : e ≠ w := fun h => hfe (by rw [h, hw2]; simp)
  have he'w : e' ≠ M.mate w := fun h => hfe' (by rw [h, M.mate_mate, hw1]; simp)
  have hdb := dartsAt_eq_of_pair he hw1 hew D1.hdeg2
  have hdb' := dartsAt_eq_of_pair he' hw2 he'w D1.hdeg2'
  have hσ : M.sigma b b' = 1 := by
    change M.bondsBetween b b' = 1
    rw [← Degen.card_neighborDarts M D1.hbb']
    unfold Degen.neighborDarts
    rw [hdb, filter_insert, if_neg (fun h => hfe (by rw [h]; simp)), filter_singleton, if_pos hw2]
    rfl
  have hAt : (closureOne M b b' x₁ x₂).atoms = M.atoms \ {b, b'} := by
    change insert (M.atom (M.mate x₁)) (insert (M.atom (M.mate x₂)) (M.atoms \ {b, b'})) = _
    rw [insert_eq_of_mem (mem_sdiff.mpr ⟨M.atom_mem _, hfx2⟩), insert_eq_of_mem (mem_sdiff.mpr ⟨M.atom_mem _, hfx1⟩)]
  refine ⟨by rw [hσ]; norm_num, ?_, loopless_molGraph hreg.loop, {s(M.atom (M.mate e), M.atom (M.mate e'))},
    Or.inr ⟨hσ, M.atom (M.mate e), M.atom (M.mate e'), ?_, ?_, rfl⟩, fun f => ?_⟩
  · show (closureOne M b b' x₁ x₂).atoms = _
    rw [hAt]
    ext z; simp only [mem_sdiff, mem_insert, mem_singleton, mem_erase]; tauto
  · unfold Molecule.groupNbrs
    rw [filter_inGroup_atoms, hdb, Finset.insert_val_of_notMem (by simpa using hew)]
    simp [hw2]
    exact Multiset.cons_swap _ _ _
  · unfold Molecule.groupNbrs
    rw [filter_inGroup_atoms, hdb', Finset.insert_val_of_notMem (by simpa using he'w)]
    simp [M.mate_mate, hw1]
    exact Multiset.cons_swap _ _ _
  · induction f using Sym2.ind with
    | _ p q =>
    rw [Multiset.count_filter, groupBonds_atoms_count, molGraph_mult, molGraph_mult, Multiset.count_singleton]
    by_cases hpq : p ∈ ({b, b'} : Finset V) ∨ q ∈ ({b, b'} : Finset V)
    · have h0 : (closureOne M b b' x₁ x₂).bondsBetween p q = 0 := by
        by_contra h
        have := bb_pos_mem (Nat.pos_of_ne_zero h)
        rw [hAt] at this
        rcases hpq with h' | h' <;> simp_all
      have hnot : ¬ (b ∉ s(p, q) ∧ b' ∉ s(p, q)) := by
        rintro ⟨h1, h2⟩
        simp only [mem_insert, mem_singleton] at hpq
        rcases hpq with (rfl | rfl) | (rfl | rfl)
        · exact h1 (Sym2.mem_mk_left _ _)
        · exact h2 (Sym2.mem_mk_left _ _)
        · exact h1 (Sym2.mem_mk_right _ _)
        · exact h2 (Sym2.mem_mk_right _ _)
      have n1 : ¬ s(p, q) = s(M.atom (M.mate e), M.atom (M.mate e')) := by
        intro h
        rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hpq with h | h <;> simp_all
      rw [h0, if_neg hnot, if_neg n1]
    · push Not at hpq
      have hin : b ∉ s(p, q) ∧ b' ∉ s(p, q) := by
        simp only [mem_insert, mem_singleton, not_or] at hpq
        refine ⟨fun h => ?_, fun h => ?_⟩ <;> rcases Sym2.mem_iff.mp h with h | h
        exacts [hpq.1.1 h.symm, hpq.2.1 h.symm, hpq.1.2 h.symm, hpq.2.2 h.symm]
      rw [bb_closureOne M b b' x₁ x₂ hpq.1 hpq.2, if_pos hin, ← hsym]
      by_cases h : s(p, q) = s(M.atom (M.mate e), M.atom (M.mate e'))
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (fun h' => h h'.symm), if_neg h]

/-- **One β-chain: `closureOne` is D11's closure (`σ = 1`).** -/
theorem isClosure_closureOne {M : Molecule V D} {cls : V → Cls} {odd : Prop} (hS : FinalShape M cls odd)
    {b b' : V} {x₁ x₂ y y' : D} (D1 : Case4OneData M cls b b' x₁ x₂ y y')
    (hreg : RegCore (closureOne M b b' x₁ x₂)) :
    M.IsClosure M.atoms b b' (molGraph (closureOne M b b' x₁ x₂)) := by
  classical
  have hx1 := mem_crossDarts.mp (show x₁ ∈ crossDarts M {b, b'} by rw [D1.hc]; simp)
  have hx2 := mem_crossDarts.mp (show x₂ ∈ crossDarts M {b, b'} by rw [D1.hc]; simp)
  obtain ⟨w, hw1, hw2⟩ := D1.hadj
  have hwK : M.atom (M.mate w) ∈ ({b, b'} : Finset V) := by rw [hw2]; simp
  have hmwK : M.atom (M.mate (M.mate w)) ∈ ({b, b'} : Finset V) := by rw [M.mate_mate, hw1]; simp
  have hcard3 : ∀ {v : V} {p q r : D}, M.deg v = 2 → M.atom p = v → M.atom q = v → M.atom r = v → p ≠ q →
      p ≠ r → q ≠ r → False := by
    intro v p q r hd hp hq hr hpq hpr hqr
    have hsub : ({p, q, r} : Finset D) ⊆ M.dartsAt v := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and]
      rcases hx with rfl | rfl | rfl
      exacts [hp, hq, hr]
    have := card_le_card hsub
    rw [card_insert_of_notMem (by simp [hpq, hpr]), card_pair hqr] at this
    unfold Molecule.deg at hd
    omega
  have hne1 : ∀ z, M.atom (M.mate z) ∈ ({b, b'} : Finset V) → x₁ ≠ z := fun z hz h => hx1.2 (h ▸ hz)
  have hne2 : ∀ z, M.atom (M.mate z) ∈ ({b, b'} : Finset V) → x₂ ≠ z := fun z hz h => hx2.2 (h ▸ hz)
  have hsplit : (M.atom x₁ = b ∧ M.atom x₂ = b') ∨ (M.atom x₁ = b' ∧ M.atom x₂ = b) := by
    have h1 := hx1.1; have h2 := hx2.1
    simp only [mem_insert, mem_singleton] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact (hcard3 D1.hdeg2 h1 h2 hw1 D1.hne (hne1 w hwK) (hne2 w hwK)).elim
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact (hcard3 D1.hdeg2' h1 h2 hw2 D1.hne (hne1 _ hmwK) (hne2 _ hmwK)).elim
  rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact isClosure_closureOne_core D1 hreg h1 h2 hw1 hw2 hx1.2 hx2.2 rfl hx1.2 hx2.2
  · exact isClosure_closureOne_core D1 hreg h2 h1 hw1 hw2 hx2.2 hx1.2 Sym2.eq_swap hx1.2 hx2.2

/-- **One β-chain with a T-route: the component is a T-vine.** -/
theorem isTVine_of_one {M : Molecule V D} {cls : V → Cls} {odd : Prop} (hS : FinalShape M cls odd)
    {b b' : V} {x₁ x₂ y y' : D} (D1 : Case4OneData M cls b b' x₁ x₂ y y')
    (hreg : RegCore (closureOne M b b' x₁ x₂)) {k : ℕ} (hroute : YRouteT k (closureOne M b b' x₁ x₂)) :
    M.IsTVine M.atoms b b' := by
  obtain ⟨G', hpath, htri⟩ := yrouteT_graph hroute hreg
  exact ⟨isBlock_atoms D1.hb D1.hb' D1.hbb' (hS.dir2 b D1.hb D1.hdeg2) (hS.dir2 b' D1.hb' D1.hdeg2') D1.hdeg4 hS.conn,
    fun u _ w _ _ => hS.noTriple u w, molGraph _, G', isClosure_closureOne hS D1 hreg, hpath, htri⟩

end one

end WaveTurbulence.GammaLow.FinalCount
