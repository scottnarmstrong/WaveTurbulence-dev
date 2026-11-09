/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.SubObjBridge
public import WaveTurbulence.Foundations.TVine.Struct.RemoveAll
import Mathlib.Tactic

/-!
# Gap freeness: from L1's `GapFree` to the molecule-level `GapFree` (packet L3)

If the two darts `x₁ ≠ x₂` of `U°` at `U.upper` disconnected `S`, the side `X` of `a` would be a 2-edge-cut whose two
bonds are exactly the two `U°`-bonds at `U.upper`, i.e. a gap cut (`GapCutAt`) of the L1 sub-object `suOf U`.

* `orep`: the outgoing dart of a bond;
* **`gapFree_of_gapFreeU`**: `Core.GapFree (groupGraph M S) (suOf U) → GapFree M S U` inside a T-vine.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core GammaLow.FinalCount

universe u v

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The outgoing dart of the bond of `x`. -/
def orep (M : Molecule V D) (x : D) : D := if M.out x = true then x else M.mate x

theorem out_orep (M : Molecule V D) (x : D) : M.out (orep M x) = true := by
  unfold orep; split_ifs with h
  · exact h
  · rw [M.out_mate]; simpa using h

theorem ends_mate (M : Molecule V D) (x : D) : M.ends (M.mate x) = M.ends x := by
  simp only [Molecule.ends, M.mate_mate]; exact Sym2.eq_swap

theorem ends_orep (M : Molecule V D) (x : D) : M.ends (orep M x) = M.ends x := by
  unfold orep; split_ifs
  · rfl
  · exact ends_mate M x

theorem inGroup_orep (M : Molecule V D) {S : Finset V} {x : D} (h : M.InGroup S x) : M.InGroup S (orep M x) := by
  unfold orep; split_ifs
  · exact h
  · exact ⟨h.2, by rw [M.mate_mate]; exact h.1⟩

theorem orep_eq_cases (M : Molecule V D) (x : D) : orep M x = x ∨ orep M x = M.mate x := by
  unfold orep; split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem orep_of_out (M : Molecule V D) {y x : D} (hy : M.out y = true) (h : y = x ∨ y = M.mate x) :
    y = orep M x := by
  unfold orep
  rcases h with rfl | rfl
  · rw [if_pos hy]
  · have : ¬ M.out x = true := by rw [M.out_mate] at hy; simpa using hy
    rw [if_neg this]

theorem orep_mem_groupDarts (M : Molecule V D) {S : Finset V} {x : D} (h : M.InGroup S x) :
    orep M x ∈ groupDarts M S :=
  (mem_groupDarts M).mpr ⟨out_orep M x, (inGroup_orep M h).1, (inGroup_orep M h).2⟩

/-- A set of outgoing darts of one bond type has at most that multiplicity. -/
theorem card_le_mult (M : Molecule V D) {S : Finset V} {e : Sym2 V} (P : Finset D)
    (hP : ∀ p ∈ P, p ∈ groupDarts M S ∧ M.ends p = e) : P.card ≤ (groupGraph M S).mult e := by
  rw [groupGraph_mult_eq_card]
  exact Finset.card_le_card fun p hp => Finset.mem_filter.mpr (hP p hp)

/-- The adjoint dart of a hyper object: not contained in it. -/
theorem adj_dart {γ : ℝ} {M : Molecule V D} (U : Src.Object γ M) (hh : (suOf U).hyper = true) :
    ∃ e : D, M.ends e = s(U.upper, U.lower) ∧ M.InGroup U.atoms e ∧
      ∀ x, U.ContainsDart x → x ≠ e ∧ x ≠ M.mate e := by
  obtain ⟨A, a, b, sh⟩ := U
  cases sh with
  | vc _ => exact absurd hh (by simp [suOf])
  | hyper R =>
    refine ⟨R.added, R.ends_eq, ?_, fun x hx => ⟨hx.1, hx.2.1⟩⟩
    have := R.ends_eq
    have hB := R.adjoint.1
    simp only [Molecule.ends, Sym2.eq_iff] at this
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by rw [h1]; exact hB.2.1, by rw [h2]; exact hB.2.2.1⟩
    · exact ⟨by rw [h1]; exact hB.2.2.1, by rw [h2]; exact hB.2.1⟩

/-- **Gap freeness at the molecule level** from L1's gap freeness, inside a T-vine. -/
theorem gapFree_of_gapFreeU {γ : ℝ} {M : Molecule V D} {S : Finset V} {j₁ j₂ : V} (hT : M.IsTVine S j₁ j₂)
    (U : Src.Object γ M) (hU : IsSubObjU (groupGraph M S) (suOf U))
    (hgap : Core.GapFree (groupGraph M S) (suOf U)) : GapFree M S U := by
  classical
  intro x₁ x₂ hne hx₁ hx₂ hc₁ hc₂ a ha b hb
  by_contra hab
  have hTU := ((isTVine_iff M).mp hT).2
  have hl := loopless_of_isTVineU hTU
  set k := U.upper with hk
  set F : Finset D := {x₁, x₂} with hF
  set X := S.filter fun w => M.ConnectedWithout S F a w with hXdef
  have hXS : X ⊆ S := Finset.filter_subset _ _
  have haX : a ∈ X := Finset.mem_filter.mpr ⟨ha, .refl _⟩
  have hbX : b ∉ X := fun h => hab (Finset.mem_filter.mp h).2
  -- darts of `U°` lie in the group of `S(U)`
  have hg₁ : M.InGroup U.atoms x₁ := containsDart_inGroup U hc₁
  have hg₂ : M.InGroup U.atoms x₂ := containsDart_inGroup U hc₂
  have hAS : U.atoms ⊆ S := hU.1.subset
  have hgS₁ : M.InGroup S x₁ := ⟨hAS hg₁.1, hAS hg₁.2⟩
  have hgS₂ : M.InGroup S x₂ := ⟨hAS hg₂.1, hAS hg₂.2⟩
  set n₁ := M.atom (M.mate x₁)
  set n₂ := M.atom (M.mate x₂)
  -- no loops
  have hnl : ∀ x, M.InGroup S x → M.atom x ≠ M.atom (M.mate x) := by
    intro x hx h
    have := groupGraph_mult_ne_zero_of_dart M hx
    simp only [Molecule.ends, h] at this
    exact this (hl _)
  have hkn₁ : k ≠ n₁ := hx₁ ▸ hnl x₁ hgS₁
  have hkn₂ : k ≠ n₂ := hx₂ ▸ hnl x₂ hgS₂
  -- the two outgoing darts differ
  have ho : orep M x₁ ≠ orep M x₂ := by
    intro h
    rcases orep_eq_cases M x₁ with h1 | h1 <;> rcases orep_eq_cases M x₂ with h2 | h2
    · exact hne (h1.symm.trans (h.trans h2))
    · have : x₁ = M.mate x₂ := h1.symm.trans (h.trans h2)
      exact hnl x₂ hgS₂ (by rw [← this, hx₁, hx₂])
    · have : M.mate x₁ = x₂ := h1.symm.trans (h.trans h2)
      exact hnl x₁ hgS₁ (by rw [this, hx₁, hx₂])
    · have : M.mate x₁ = M.mate x₂ := h1.symm.trans (h.trans h2)
      exact hne (by have := congrArg M.mate this; simpa only [M.mate_mate] using this)
  -- crossing darts are the two bonds of `F`
  have hcross : crossDarts M S X ⊆ {orep M x₁, orep M x₂} := by
    intro y hy
    obtain ⟨hyG, hyc⟩ := Finset.mem_filter.mp hy
    obtain ⟨hyo, hya, hym⟩ := (mem_groupDarts M).mp hyG
    by_cases hyF : y ∈ F ∨ M.mate y ∈ F
    · simp only [hF, Finset.mem_insert, Finset.mem_singleton] at hyF
      have hy' : (y = x₁ ∨ y = M.mate x₁) ∨ (y = x₂ ∨ y = M.mate x₂) := by
        rcases hyF with (h | h) | (h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl (Or.inr (by rw [← h, M.mate_mate]))
        · exact Or.inr (Or.inr (by rw [← h, M.mate_mate]))
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hy' with h | h
      · exact Or.inl (orep_of_out M hyo h)
      · exact Or.inr (orep_of_out M hyo h)
    · exfalso
      push_neg at hyF
      have hstep : M.ConnectedWithout S F (M.atom y) (M.atom (M.mate y)) :=
        .rel _ _ ⟨y, ⟨hya, hym⟩, hyF.1, hyF.2, rfl, rfl⟩
      by_cases hin : M.atom y ∈ X
      · have hc := (Finset.mem_filter.mp hin).2
        exact (hyc.mp hin) (Finset.mem_filter.mpr ⟨hym, .trans _ _ _ hc hstep⟩)
      · have hout : M.atom (M.mate y) ∈ X := by
          by_contra h'; exact hin (hyc.mpr h')
        have hc := (Finset.mem_filter.mp hout).2
        exact hin (Finset.mem_filter.mpr ⟨hya, .trans _ _ _ hc (.symm _ _ hstep)⟩)
  -- the cut is `2`, and both bonds cross
  have hC := cutCtx_of_isTVineU hTU
  have h2 : 2 ≤ cut (groupGraph M S) X := two_le_cut hC hXS haX hb hbX
  rw [cut_groupGraph M hXS] at h2
  have hle : (crossDarts M S X).card ≤ 2 := (Finset.card_le_card hcross).trans (Finset.card_le_two)
  have hceq : crossDarts M S X = {orep M x₁, orep M x₂} :=
    Finset.eq_of_subset_of_card_le hcross (by rw [Finset.card_pair ho]; omega)
  have hcut2 : cut (groupGraph M S) X = 2 := by
    rw [cut_groupGraph M hXS, hceq, Finset.card_pair ho]
  have hcr : ∀ x, orep M x ∈ crossDarts M S X → (M.atom x ∈ X ↔ M.atom (M.mate x) ∉ X) := by
    intro x hx
    have := (Finset.mem_filter.mp hx).2
    rcases orep_eq_cases M x with h | h
    · rwa [h] at this
    · rw [h, M.mate_mate] at this
      constructor
      · intro h1 h2; exact (this.mp h2) h1
      · intro h1; by_contra h2; exact h1 (this.mpr h2)
  have hcr₁ := hcr x₁ (by rw [hceq]; simp)
  have hcr₂ := hcr x₂ (by rw [hceq]; simp)
  rw [hx₁] at hcr₁
  rw [hx₂] at hcr₂
  -- the neighbours of `k` in `U°` are `n₁, n₂`
  have hkU : k = (suOf U).k₁ := rfl
  have hdeg : deg ((suOf U).core (groupGraph M S)) k = 2 := hU.2.2.2.2.2.1
  have hnbrs : nbrs ((suOf U).core (groupGraph M S)) k = {n₁, n₂} := by
    symm
    refine Multiset.eq_of_le_of_card_le ?_ (by rw [card_nbrs, hdeg]; simp)
    rw [Multiset.le_iff_count]
    intro w
    have hloop : ((suOf U).core (groupGraph M S)).mult s(k, k) = 0 := by
      rw [core_mult]; split_ifs <;> simp [hl k]
    rw [count_nbrs, core_verts, hloop, ite_self, add_zero]
    · split_ifs with hwA
      · rw [core_mult, if_pos (Finset.mem_sym2_iff.mpr fun z hz => by
            rcases Sym2.mem_iff.mp hz with rfl | rfl
            · rw [← hx₁]; exact hg₁.1
            · exact hwA)]
        -- the outgoing darts of `x₁, x₂` with far end `w`
        set Q := ({orep M x₁, orep M x₂} : Finset D).filter fun o => M.ends o = s(k, w)
        have hQ : ∀ p ∈ Q, p ∈ groupDarts M S ∧ M.ends p = s(k, w) := by
          intro p hp
          obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp1
          rcases hp1 with rfl | rfl
          · exact ⟨orep_mem_groupDarts M hgS₁, hp2⟩
          · exact ⟨orep_mem_groupDarts M hgS₂, hp2⟩
        have he₁ : M.ends (orep M x₁) = s(k, n₁) := by
          rw [ends_orep]; show s(M.atom x₁, M.atom (M.mate x₁)) = s(k, n₁); rw [hx₁]
        have he₂ : M.ends (orep M x₂) = s(k, n₂) := by
          rw [ends_orep]; show s(M.atom x₂, M.atom (M.mate x₂)) = s(k, n₂); rw [hx₂]
        have hcount : Multiset.count w {n₁, n₂} ≤ Q.card := by
          have hm₁ : n₁ = w → orep M x₁ ∈ Q := fun h =>
            Finset.mem_filter.mpr ⟨by simp, by rw [he₁, h]⟩
          have hm₂ : n₂ = w → orep M x₂ ∈ Q := fun h =>
            Finset.mem_filter.mpr ⟨by simp, by rw [he₂, h]⟩
          rw [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
          by_cases h1 : w = n₁ <;> by_cases h2 : w = n₂
          · rw [if_pos h1, if_pos h2]
            have hsub : ({orep M x₁, orep M x₂} : Finset D) ⊆ Q := by
              intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
              rcases hp with rfl | rfl
              · exact hm₁ h1.symm
              · exact hm₂ h2.symm
            have := Finset.card_le_card hsub
            rw [Finset.card_pair ho] at this
            omega
          · rw [if_pos h1, if_neg h2]
            have := Finset.card_pos.mpr ⟨_, hm₁ h1.symm⟩; omega
          · rw [if_neg h1, if_pos h2]
            have := Finset.card_pos.mpr ⟨_, hm₂ h2.symm⟩; omega
          · rw [if_neg h1, if_neg h2]; omega
        split_ifs with hhyp
        · -- hyper: the adjoint's outgoing dart is a further dart of type `s(k, w)`
          obtain ⟨e, hee, heA, hex⟩ := adj_dart U hhyp.1
          have hadj : M.ends e = s(k, w) := by rw [hee]; exact hhyp.2.symm
          have hRS : M.InGroup S e := ⟨hAS heA.1, hAS heA.2⟩
          have hnot : orep M e ∉ Q := by
            intro hq
            obtain ⟨hq1, -⟩ := Finset.mem_filter.mp hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq1
            have key : ∀ x, (x ≠ e ∧ x ≠ M.mate e) → orep M e ≠ orep M x := by
              intro x hx h
              rcases orep_eq_cases M e with h1 | h1 <;> rcases orep_eq_cases M x with h2 | h2
              · exact hx.1 (h2.symm.trans (h.symm.trans h1))
              · exact hx.2 (by rw [← h1, h, h2, M.mate_mate])
              · exact hx.2 (by rw [← h2, ← h, h1])
              · exact hx.1 (by have h3 := (h1.symm.trans (h.trans h2)); have h4 := congrArg M.mate h3
                               simpa only [M.mate_mate] using h4.symm)
            rcases hq1 with h | h
            · exact key x₁ (hex x₁ hc₁) h
            · exact key x₂ (hex x₂ hc₂) h
          have := card_le_mult M (e := s(k, w)) (Finset.cons (orep M e) Q hnot) (by
            intro p hp
            rcases Finset.mem_cons.mp hp with rfl | hp
            · exact ⟨orep_mem_groupDarts M hRS, by rw [ends_orep]; exact hadj⟩
            · exact hQ p hp)
          rw [Finset.card_cons] at this
          have := hcount
          omega
        · exact hcount.trans (card_le_mult M Q hQ)
      · have hn : w ≠ n₁ ∧ w ≠ n₂ := ⟨fun h => hwA (h ▸ hg₁.2), fun h => hwA (h ▸ hg₂.2)⟩
        simp [hn.1, hn.2]
  exact hgap ⟨X, hXS, hcut2, n₁, n₂, hnbrs, hcr₁, hcr₂⟩

end WaveTurbulence.TVine.Struct
