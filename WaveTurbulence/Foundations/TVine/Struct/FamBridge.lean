/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Families2
public import WaveTurbulence.Foundations.TVine.Struct.GapBridge
import Mathlib.Tactic

/-!
# (F5) for families at the molecule level, and Cor 1.16′ (packet L3)

* `remAdj_of_removeAll`: a bond of `removeAll (groupGraph M S) (suOf ∘ U)` is a `remAdj` step (a kept adjoint is the
  adjoint dart of its hyper member);
* **`tvineFamilies_of`**: `TVineFamiliesStatement` from `Thm115Inputs`;
* **`cor116Single`**: `Cor116SingleStatement` from `Thm115Inputs`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core GammaLow.FinalCount

universe u v

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem inner_suOf {γ : ℝ} {M : Molecule V D} (U : Src.Object γ M) :
    (suOf U).inner = U.atoms \ {U.upper, U.lower} := by
  ext x
  simp only [SubObj.inner, suOf, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem remAtoms_eq {γ : ℝ} {M : Molecule V D} (S : Finset V) {n : ℕ} (U : Fin n → Src.Object γ M) :
    remAtoms S U = S \ Checker.innerAll (List.ofFn fun i => suOf (U i)) := by
  ext x
  simp only [remAtoms, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_univ, true_and, mem_innerAll,
    List.mem_ofFn]
  constructor
  · rintro ⟨hx, hn⟩
    refine ⟨hx, ?_⟩
    rintro ⟨W, ⟨i, rfl⟩, hxi⟩
    rw [inner_suOf, Finset.mem_sdiff] at hxi
    exact hn ⟨i, hxi⟩
  · rintro ⟨hx, hn⟩
    refine ⟨hx, ?_⟩
    rintro ⟨i, hxi⟩
    exact hn ⟨_, ⟨i, rfl⟩, by rw [inner_suOf, Finset.mem_sdiff]; exact hxi⟩

/-- **A surviving bond is a `remAdj` step.** -/
theorem remAdj_of_removeAll {γ : ℝ} (hγ : γ ≤ 1 / 2) {M : Molecule V D} {S : Finset V} {n : ℕ}
    (U : Fin n → Src.Object γ M) (hsub : ∀ i, (U i).atoms ⊂ S)
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i).atoms (U j).atoms) {p q : V}
    (h : AdjIn (removeAll (groupGraph M S) (List.ofFn fun i => suOf (U i)))
      (removeAll (groupGraph M S) (List.ofFn fun i => suOf (U i))).verts p q) : remAdj M S U p q := by
  classical
  set Us := List.ofFn fun i => suOf (U i)
  set G := groupGraph M S
  have hsubA : ∀ W ∈ Us, W.atoms ⊆ G.verts := by
    intro W hW; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hW; exact (hsub i).subset
  have hpw : Us.Pairwise (fun U W => Disjoint U.atoms W.atoms) :=
    List.pairwise_ofFn.mpr fun i j hij => hdisj i j (ne_of_lt hij)
  obtain ⟨hv, hm⟩ := removeAll_eq G Us hsubA hpw
  obtain ⟨hp, hq, hmult⟩ := h
  rw [hm, ← hv, if_pos (Finset.mem_sym2_iff.mpr fun z hz => by
    rcases Sym2.mem_iff.mp hz with rfl | rfl
    · exact hp
    · exact hq)] at hmult
  have hpS : p ∈ S := (Finset.mem_sdiff.mp (hv ▸ hp)).1
  have hqS : q ∈ S := (Finset.mem_sdiff.mp (hv ▸ hq)).1
  have hsum : (Us.map fun W => (W.core G).mult s(p, q)).sum = ∑ i, ((suOf (U i)).core G).mult s(p, q) := by
    rw [List.map_ofFn, List.sum_ofFn]; rfl
  rw [hsum] at hmult
  by_cases hin : ∃ i, s(p, q) ∈ (U i).atoms.sym2
  · obtain ⟨i, hi⟩ := hin
    have hpi : p ∈ (U i).atoms := Finset.mem_sym2_iff.mp hi p (Sym2.mem_mk_left p q)
    have hothers : ∀ j, j ≠ i → ((suOf (U j)).core G).mult s(p, q) = 0 := by
      intro j hj
      refine core_mult_of_not_mem G _ fun hj' => ?_
      exact Finset.disjoint_left.mp (hdisj i j (Ne.symm hj)) hpi
        (Finset.mem_sym2_iff.mp hj' p (Sym2.mem_mk_left p q))
    rw [Finset.sum_eq_single i (fun j _ hj => hothers j hj) (by simp), core_mult,
      if_pos (show s(p, q) ∈ (suOf (U i)).atoms.sym2 from hi)] at hmult
    split_ifs at hmult with hh
    · obtain ⟨e, hee, heA, hex⟩ := adj_dart (U i) hh.1
      have hpq : M.ends e = s(p, q) := hee.trans hh.2.symm
      have hx : ∃ x, (x = e ∨ x = M.mate e) ∧ M.atom x = p ∧ M.atom (M.mate x) = q := by
        simp only [Molecule.ends, Sym2.eq_iff] at hpq
        rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨e, Or.inl rfl, h1, h2⟩
        · exact ⟨M.mate e, Or.inr rfl, h2, by rw [M.mate_mate]; exact h1⟩
      obtain ⟨x, hxe, hxp, hxq⟩ := hx
      refine ⟨x, ⟨by rw [hxp]; exact hpS, by rw [hxq]; exact hqS⟩, fun j hc => ?_, hxp, hxq⟩
      by_cases hji : j = i
      · subst hji
        obtain ⟨h1, h2⟩ := hex x hc
        rcases hxe with h | h
        · exact h1 h
        · exact h2 h
      · have hg := containsDart_inGroup (U j) hc
        exact Finset.disjoint_left.mp (hdisj i j (Ne.symm hji)) hpi (hxp ▸ hg.1)
    · omega
  · push_neg at hin
    have hzero : ∀ i, ((suOf (U i)).core G).mult s(p, q) = 0 := fun i => core_mult_of_not_mem G _ (hin i)
    rw [Finset.sum_eq_zero fun i _ => hzero i, Nat.sub_zero] at hmult
    obtain ⟨x, hx, hxp, hxq⟩ := (adjIn_groupGraph_iff M).mp ⟨hpS, hqS, hmult⟩
    refine ⟨x, hx, fun i hc => ?_, hxp, hxq⟩
    have hg := containsDart_inGroup (U i) hc
    exact hin i (Finset.mem_sym2_iff.mpr fun z hz => by
      rcases Sym2.mem_iff.mp hz with rfl | rfl
      · exact hxp ▸ hg.1
      · exact hxq ▸ hg.2)

/-- **N2 Theorem 1.15 (F5) for families, molecule level** (sources' semantics). -/
theorem tvineFamilies_of (I : Thm115Inputs.{u}) : TVineFamiliesStatement.{u, v} := by
  intro V D _ _ _ M γ hγ S j₁ j₂ hT n U hsub hdisj
  classical
  have hTU := ((isTVine_iff M).mp hT).2
  set Us := List.ofFn fun i => suOf (U i)
  set G := groupGraph M S
  have hsubU : ∀ W ∈ Us, IsSubObjU G W := by
    intro W hW; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hW; exact subObj_suOf hγ (U i) (hsub i)
  have hsubA : ∀ W ∈ Us, W.atoms ⊆ G.verts := fun W hW => (hsubU W hW).1.subset
  have hpw : Us.Pairwise (fun U W => Disjoint U.atoms W.atoms) :=
    List.pairwise_ofFn.mpr fun i j hij => hdisj i j (ne_of_lt hij)
  have hconn := families I _ G j₁ j₂ Us rfl hTU hsubU hpw
  obtain ⟨hv, -⟩ := removeAll_eq G Us hsubA hpw
  have hrem : remAtoms S U = (removeAll G Us).verts := by rw [hv, remAtoms_eq]; rfl
  intro a ha b hb
  rw [hrem] at ha hb
  have hr := hconn a ha b hb
  clear ha hb
  induction hr with
  | refl => exact .refl _
  | tail _ hbc ih => exact .trans _ _ _ ih (.rel _ _ (remAdj_of_removeAll hγ U hsub hdisj hbc))

/-- **N3 Corollary 1.16′ (1)–(3) for a single-vine container** (= L6 `Cor116PrimeInput`). -/
theorem cor116Single (I : Thm115Inputs.{u}) : Cor116SingleStatement.{u, v} :=
  cor116Single_of I containerJointsInput_holds (tvineFamilies_of I)

end WaveTurbulence.TVine.Struct
