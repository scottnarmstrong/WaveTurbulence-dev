/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.F6Concat
import Mathlib.Tactic

/-!
# N2 Theorem 1.15 (F6), U level (packet L3)

Two vine-like sub-objects `U, W` of a T-vine whose atom sets `A, B` overlap without nesting are double bonds sharing
exactly one atom. Write `P = A ∩ B`. Only the joints of `U` have bonds leaving `A` (two each, one for hyper type).
* both joints of `U` and of `W` lie in `P`: `A ∖ B` and `B ∖ A` are disjoint joint-free 2-poles (`cutQ_two`),
  contradicting N3 Lemma 6.2;
* both joints of `W` in `P`, at most one of `U`: that joint is a cut atom of the T-vine (`cut_atom_false`), contradicting
  N3 Lemma 4.1;
* one joint of each in `P` (`one_joint`; both members are then of block type):
  - the same atom `k`: `P = {k}` and `U ∪ W` is a concatenation, so both are (I) (`concat_allowed`);
  - different atoms: `W` has a cut atom, so it is a VC:I+I whose far double bond `Y` concatenates with `U`; then `U` would
    be (I), but it has three atoms.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core

universe u

variable {V : Type u} [DecidableEq V]

theorem induce_mult_le (G : UMultigraph V) (S : Finset V) (e : Sym2 V) : (induce G S).mult e ≤ G.mult e := by
  show (if e ∈ S.sym2 then G.mult e else 0) ≤ _
  split_ifs <;> simp

theorem core_le (G : UMultigraph V) (U : SubObj V) (e : Sym2 V) : (U.core G).mult e ≤ G.mult e :=
  (core_mult_le G U e).trans (induce_mult_le G _ e)

theorem induce_self (H : UMultigraph V) : induce H H.verts = H := by
  refine Core.ext rfl fun e => ?_
  show (if e ∈ H.verts.sym2 then H.mult e else 0) = H.mult e
  split_ifs with h
  · rfl
  · by_contra hne; exact h (mem_sym2_of_mult_ne_zero H (Ne.symm hne))

section

variable {G : UMultigraph V} {j₁ j₂ : V}

/-- Bonds leaving `S(U)`: at most two at a joint (one for hyper type), none elsewhere. -/
theorem out_bound (hT : IsTVineU G j₁ j₂) {U : SubObj V} (hU : IsSubObjU G U) {x : V} (hx : x ∈ U.atoms) :
    ∑ y ∈ G.verts \ U.atoms, G.mult s(x, y) ≤
      if x = U.k₁ ∨ x = U.k₂ then (if U.hyper = true then 1 else 2) else 0 := by
  have hA : U.atoms ⊆ G.verts := hU.1.subset
  have h1 := deg_induce G hx hA
  have h4 := deg_four hT hU hx
  have hci := deg_core_le_induce G U x
  rcases core_deg_cases hU hx with ⟨hj, h2⟩ | ⟨hn1, hn2, h2⟩
  · rw [if_pos hj]
    cases hh : U.hyper with
    | false => simp only [Bool.false_eq_true, if_false]; omega
    | true =>
      have := deg_core_hyper hU hh hj
      simp only [if_true]; omega
  · rw [if_neg (by tauto)]; omega

theorem joint_of_out (hB : IsBlockU G j₁ j₂) {U : SubObj V} (hU : IsSubObjU G U) {x y : V} (hx : x ∈ U.atoms)
    (hy : y ∈ G.verts) (hyA : y ∉ U.atoms) (hm : G.mult s(x, y) ≠ 0) : x = U.k₁ ∨ x = U.k₂ := by
  by_contra h
  push_neg at h
  exact hyA (mem_of_inner_bond hB hU hx h.1 h.2 hy hm)

/-- **The core of a sub-object crosses any proper part of it twice.** -/
theorem cross_two (hT : IsTVineU G j₁ j₂) {U : SubObj V} (hU : IsSubObjU G U) {P : Finset V} (hP : P ⊆ U.atoms)
    {p q : V} (hp : p ∈ P) (hq : q ∈ U.atoms) (hqP : q ∉ P) :
    2 ≤ ∑ x ∈ P, ∑ y ∈ U.atoms \ P, G.mult s(x, y) := by
  have hl : G.Loopless := loopless_of_isTVineU hT
  have hlc : (U.core G).Loopless := fun v => Nat.le_zero.mp ((core_le G U _).trans (hl v).le)
  have hC := cutCtx_of_isBlockU hU.2.2 hlc
  have h2 := two_le_cut hC (by rw [core_verts]; exact hP) hp (by rw [core_verts]; exact hq) hqP
  unfold cut at h2
  rw [core_verts] at h2
  exact h2.trans (Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => core_le G U _)

theorem sum_ite_two_le (S : Finset V) (a b : V) :
    ∑ x ∈ S, (if x = a ∨ x = b then 2 else 0) ≤ 4 := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  have : (S.filter fun x => x = a ∨ x = b).card ≤ 2 := by
    refine (Finset.card_le_card fun x hx => ?_).trans (Finset.card_le_two (a := a) (b := b))
    rcases (Finset.mem_filter.mp hx).2 with rfl | rfl <;> simp
  omega

/-- **Case: all four joints in `P`.** Then `A ∖ B` is a 2-pole. -/
theorem cutQ_two (hT : IsTVineU G j₁ j₂) {U W : SubObj V} (hU : IsSubObjU G U) (hW : IsSubObjU G W)
    (hUin : U.k₁ ∈ W.atoms ∧ U.k₂ ∈ W.atoms) (hWin : W.k₁ ∈ U.atoms ∧ W.k₂ ∈ U.atoms) {q : V}
    (hq : q ∈ U.atoms \ W.atoms) : cut G (U.atoms \ W.atoms) = 2 := by
  classical
  have hB := hT.1
  have hAV : U.atoms ⊆ G.verts := hU.1.subset
  have hBV : W.atoms ⊆ G.verts := hW.1.subset
  set A := U.atoms
  set Bs := W.atoms
  set P := A ∩ Bs
  set Q := A \ Bs
  set O := G.verts \ (A ∪ Bs)
  have hinU : ∀ x ∈ Q, x ≠ U.k₁ ∧ x ≠ U.k₂ := fun x hx =>
    ⟨fun h => (Finset.mem_sdiff.mp hx).2 (h ▸ hUin.1), fun h => (Finset.mem_sdiff.mp hx).2 (h ▸ hUin.2)⟩
  have hinW : ∀ x ∈ Bs \ A, x ≠ W.k₁ ∧ x ≠ W.k₂ := fun x hx =>
    ⟨fun h => (Finset.mem_sdiff.mp hx).2 (h ▸ hWin.1), fun h => (Finset.mem_sdiff.mp hx).2 (h ▸ hWin.2)⟩
  -- the cut of `Q`
  have hcutQ : cut G Q = ∑ x ∈ P, ∑ y ∈ Q, G.mult s(x, y) := by
    unfold cut
    have : ∀ x ∈ Q, ∑ y ∈ G.verts \ Q, G.mult s(x, y) = ∑ y ∈ P, G.mult s(x, y) := by
      intro x hx
      symm
      refine Finset.sum_subset (fun y hy => Finset.mem_sdiff.mpr ⟨hAV (Finset.mem_inter.mp hy).1,
        fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_inter.mp hy).2⟩) fun y hy hyP => ?_
      by_contra hne
      have hyA := mem_of_inner_bond hB hU (Finset.mem_sdiff.mp hx).1 (hinU x hx).1 (hinU x hx).2
        (Finset.mem_sdiff.mp hy).1 hne
      have hyB : y ∈ Bs := by
        by_contra hyB; exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_sdiff.mpr ⟨hyA, hyB⟩)
      exact hyP (Finset.mem_inter.mpr ⟨hyA, hyB⟩)
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [Sym2.eq_swap]
  -- the cut of `A ∪ B`
  have hcutAB : cut G (A ∪ Bs) = ∑ x ∈ P, ∑ y ∈ O, G.mult s(x, y) := by
    unfold cut
    symm
    refine Finset.sum_subset (fun x hx => Finset.mem_union_left _ (Finset.mem_inter.mp hx).1) fun x hx hxP => ?_
    apply Finset.sum_eq_zero
    intro y hy
    by_contra hne
    have hyAB := (Finset.mem_sdiff.mp hy).2
    rcases Finset.mem_union.mp hx with hxA | hxB
    · have hxQ : x ∈ Q := Finset.mem_sdiff.mpr ⟨hxA, fun h => hxP (Finset.mem_inter.mpr ⟨hxA, h⟩)⟩
      exact hyAB (Finset.mem_union_left _ (mem_of_inner_bond hB hU hxA (hinU x hxQ).1 (hinU x hxQ).2
        (Finset.mem_sdiff.mp hy).1 hne))
    · have hxR : x ∈ Bs \ A := Finset.mem_sdiff.mpr ⟨hxB, fun h => hxP (Finset.mem_inter.mpr ⟨h, hxB⟩)⟩
      exact hyAB (Finset.mem_union_right _ (mem_of_inner_bond hB hW hxB (hinW x hxR).1 (hinW x hxR).2
        (Finset.mem_sdiff.mp hy).1 hne))
  -- the bonds leaving `B` at `P`
  have hout : ∑ x ∈ P, (∑ y ∈ Q, G.mult s(x, y) + ∑ y ∈ O, G.mult s(x, y)) ≤ 4 := by
    refine (Finset.sum_le_sum fun x hx => ?_).trans (sum_ite_two_le P W.k₁ W.k₂)
    have hdisj : Disjoint Q O := by
      rw [Finset.disjoint_left]; intro y hyQ hyO
      exact (Finset.mem_sdiff.mp hyO).2 (Finset.mem_union_left _ (Finset.mem_sdiff.mp hyQ).1)
    rw [← Finset.sum_union hdisj]
    refine le_trans (Finset.sum_le_sum_of_subset (fun y hy => ?_)) ((out_bound hT hW
      (Finset.mem_inter.mp hx).2).trans ?_)
    · rcases Finset.mem_union.mp hy with hy | hy
      · exact Finset.mem_sdiff.mpr ⟨hAV (Finset.mem_sdiff.mp hy).1, (Finset.mem_sdiff.mp hy).2⟩
      · exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hy).1,
          fun h => (Finset.mem_sdiff.mp hy).2 (Finset.mem_union_right _ h)⟩
    · split_ifs <;> simp
  rw [Finset.sum_add_distrib] at hout
  have hC := cutCtx_of_isTVineU hT
  have hj₁ : j₁ ∉ A ∪ Bs := fun h => by
    rcases Finset.mem_union.mp h with h | h
    · exact (joints_out hT hU).1 h
    · exact (joints_out hT hW).1 h
  have h2AB : 2 ≤ cut G (A ∪ Bs) := two_le_cut hC (Finset.union_subset hAV hBV)
    (Finset.mem_union_left _ (Finset.mem_sdiff.mp hq).1) hB.1 hj₁
  have h2Q : 2 ≤ cut G Q := two_le_cut hC (fun x hx => hAV (Finset.mem_sdiff.mp hx).1) hq hB.1
    (fun h => (joints_out hT hU).1 (Finset.mem_sdiff.mp h).1)
  omega

/-- **Case: both joints of `W` in `A`, at most one joint `k` of `U` in `B`.** Then `k` is a cut atom. -/
theorem cut_atom_false (hT : IsTVineU G j₁ j₂) {U W : SubObj V} (hU : IsSubObjU G U) (hW : IsSubObjU G W)
    (hWin : W.k₁ ∈ U.atoms ∧ W.k₂ ∈ U.atoms) {q : V} (hq : q ∈ W.atoms \ U.atoms) {k : V} (hk : k ∈ U.atoms)
    (huniq : ∀ x ∈ U.atoms ∩ W.atoms, (x = U.k₁ ∨ x = U.k₂) → x = k) : False := by
  have hB := hT.1
  have hAV : U.atoms ⊆ G.verts := hU.1.subset
  have hk₁ : k ≠ j₁ := fun h => (joints_out hT hU).1 (h ▸ hk)
  have hk₂ : k ≠ j₂ := fun h => (joints_out hT hU).2 (h ▸ hk)
  have hcut := noCutVertex_holds G j₁ j₂ hT k
    (Finset.mem_erase.mpr ⟨hk₂, Finset.mem_erase.mpr ⟨hk₁, hAV hk⟩⟩)
  set R := W.atoms \ U.atoms
  have hRsub : R ⊆ G.verts.erase k := fun x hx => Finset.mem_erase.mpr
    ⟨fun h => (Finset.mem_sdiff.mp hx).2 (h ▸ hk), hW.1.subset (Finset.mem_sdiff.mp hx).1⟩
  have hcl : ∀ x ∈ R, ∀ w ∈ G.verts.erase k, G.mult s(x, w) ≠ 0 → w ∈ R := by
    intro x hx w hw hm
    obtain ⟨hxB, hxA⟩ := Finset.mem_sdiff.mp hx
    have hx1 : x ≠ W.k₁ := fun h => hxA (h ▸ hWin.1)
    have hx2 : x ≠ W.k₂ := fun h => hxA (h ▸ hWin.2)
    have hwB := mem_of_inner_bond hB hW hxB hx1 hx2 (Finset.mem_erase.mp hw).2 hm
    refine Finset.mem_sdiff.mpr ⟨hwB, fun hwA => ?_⟩
    have hj := joint_of_out hB hU hwA (hW.1.subset hxB) hxA (by rw [Sym2.eq_swap]; exact hm)
    exact (Finset.mem_erase.mp hw).1 (huniq w (Finset.mem_inter.mpr ⟨hwA, hwB⟩) hj)
  have := eq_of_closed' hcut hRsub ⟨q, hq⟩ hcl
  have hj₁R : j₁ ∈ R := by rw [this]; exact Finset.mem_erase.mpr ⟨hk₁.symm, hB.1⟩
  exact (joints_out hT hW).1 (Finset.mem_sdiff.mp hj₁R).1

/-- **Case: at most one joint of `U` in `B`.** It exists, `U` is of block type, and it carries two bonds into
`B ∖ A`. -/
theorem one_joint (hT : IsTVineU G j₁ j₂) {U W : SubObj V} (hU : IsSubObjU G U) (hW : IsSubObjU G W)
    (hnot : ¬ (U.k₁ ∈ W.atoms ∧ U.k₂ ∈ W.atoms)) {p q : V} (hp : p ∈ U.atoms ∩ W.atoms)
    (hq : q ∈ W.atoms \ U.atoms) :
    ∃ k, k ∈ U.atoms ∩ W.atoms ∧ (k = U.k₁ ∨ k = U.k₂) ∧ U.hyper = false ∧
      2 ≤ ∑ y ∈ W.atoms \ U.atoms, G.mult s(k, y) ∧
      ∀ x ∈ U.atoms ∩ W.atoms, (x = U.k₁ ∨ x = U.k₂) → x = k := by
  classical
  have hB := hT.1
  have hAV : U.atoms ⊆ G.verts := hU.1.subset
  have hBV : W.atoms ⊆ G.verts := hW.1.subset
  have hdiff : W.atoms \ (U.atoms ∩ W.atoms) = W.atoms \ U.atoms := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  have h2 := cross_two hT hW (P := U.atoms ∩ W.atoms) Finset.inter_subset_right hp
    (Finset.mem_sdiff.mp hq).1 (fun h => (Finset.mem_sdiff.mp hq).2 (Finset.mem_inter.mp h).1)
  rw [hdiff] at h2
  obtain ⟨k, hk, hkpos⟩ : ∃ k ∈ U.atoms ∩ W.atoms, 0 < ∑ y ∈ W.atoms \ U.atoms, G.mult s(k, y) := by
    by_contra h
    push_neg at h
    have : ∑ x ∈ U.atoms ∩ W.atoms, ∑ y ∈ W.atoms \ U.atoms, G.mult s(x, y) = 0 :=
      Finset.sum_eq_zero fun x hx => Nat.le_zero.mp (h x hx)
    omega
  have hkj : k = U.k₁ ∨ k = U.k₂ := by
    obtain ⟨y, hy, hyne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.pos_iff_ne_zero.mp hkpos)
    exact joint_of_out hB hU (Finset.mem_inter.mp hk).1 (hBV (Finset.mem_sdiff.mp hy).1)
      (Finset.mem_sdiff.mp hy).2 hyne
  have huniq : ∀ x ∈ U.atoms ∩ W.atoms, (x = U.k₁ ∨ x = U.k₂) → x = k := by
    intro x hx hxj
    by_contra hxk
    apply hnot
    have hne := hU.2.2.2.2.1
    have hkB := (Finset.mem_inter.mp hk).2
    have hxB := (Finset.mem_inter.mp hx).2
    rcases hkj with rfl | rfl <;> rcases hxj with rfl | rfl
    · exact absurd rfl hxk
    · exact ⟨hkB, hxB⟩
    · exact ⟨hxB, hkB⟩
    · exact absurd rfl hxk
  -- the other atoms of `P` send nothing into `B ∖ A`
  have hsum : ∑ x ∈ U.atoms ∩ W.atoms, ∑ y ∈ W.atoms \ U.atoms, G.mult s(x, y) =
      ∑ y ∈ W.atoms \ U.atoms, G.mult s(k, y) := by
    refine Finset.sum_eq_single_of_mem k hk fun x hx hxk => Finset.sum_eq_zero fun y hy => ?_
    by_contra hne
    exact hxk (huniq x hx (joint_of_out hB hU (Finset.mem_inter.mp hx).1 (hBV (Finset.mem_sdiff.mp hy).1)
      (Finset.mem_sdiff.mp hy).2 hne))
  rw [hsum] at h2
  have hle : ∑ y ∈ W.atoms \ U.atoms, G.mult s(k, y) ≤ ∑ y ∈ G.verts \ U.atoms, G.mult s(k, y) :=
    Finset.sum_le_sum_of_subset fun y hy =>
      Finset.mem_sdiff.mpr ⟨hBV (Finset.mem_sdiff.mp hy).1, (Finset.mem_sdiff.mp hy).2⟩
  have hob := out_bound hT hU (Finset.mem_inter.mp hk).1
  rw [if_pos hkj] at hob
  refine ⟨k, hk, hkj, ?_, h2, huniq⟩
  cases hh : U.hyper with
  | false => rfl
  | true => rw [hh] at hob; simp only [if_true] at hob; omega

end

end WaveTurbulence.TVine.Struct
