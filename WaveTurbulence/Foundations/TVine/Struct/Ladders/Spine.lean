/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Ladders.Cut
import Mathlib.Tactic

/-!
# The spine and the pendant of a T-vine as runs (packet L3-LAD)

From the atom-level layer structure (`LayervineStructure`, N3 Theorem 6 (ii)–(iii)), packaged with the T-vine
context as `LV`:

* `LV.spine_bound`: every bond leaving a spine piece `G_i` goes to `G_{i-1}`, `G_{i+1}` (joints included) or to the
  pendant `H`;
* `exits_bound`: a set outside `H` receives at most one bond of `H` per outer end `x, x'` it contains;
* `LV.rung_neighbors`, `LV.junction_H`: a rung spine piece without pendant bonds is joined to both neighbours by
  `2` bonds; a junction spine piece (cut `6`) receives `≥ 2` pendant bonds;
* `LV.spine_step` (N3 L295–L296): consecutive rung spine pieces joined by 2 bonds form a ladder step. The cut is the
  `v₁`-side `C` of `S ∖ G_i`: its bonds all go to `G_i`, the `v₂`-side takes `≥ 2` of the 4 bonds of `G_i`, so
  `C` has exactly the two bonds to `G_{i+1}`; then `TV.matchStep_of_cut`;
* `LV.pend_step`: consecutive rung pendant pieces form a ladder step (the cut is `H_{k+1}`);
* `LV.run_slice`: a slice of the spine of rung pieces joined by 2 bonds is a run.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct.Ladders

open Finset

universe u v

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-! ## The extended spine as a function of the index -/

/-- The `k`-th member of the extended spine `(v₂, G₁, …, G_r, v₁)` (`∅` past the end). -/
def eS (j₁ j₂ : V) (sp : List (Finset V)) (k : ℕ) : Finset V := (extSpine j₁ j₂ sp).getD k ∅

theorem extSpine_length (j₁ j₂ : V) (sp : List (Finset V)) : (extSpine j₁ j₂ sp).length = sp.length + 2 := by
  simp [extSpine]

theorem eS_eq_getElem (j₁ j₂ : V) (sp : List (Finset V)) (k : ℕ) (hk : k < (extSpine j₁ j₂ sp).length) :
    eS j₁ j₂ sp k = (extSpine j₁ j₂ sp)[k] := by
  simp [eS, List.getD_eq_getElem?_getD, hk]

theorem get_extSpine (j₁ j₂ : V) (sp : List (Finset V)) (k : ℕ) (hk : k < (extSpine j₁ j₂ sp).length) :
    (extSpine j₁ j₂ sp).get ⟨k, hk⟩ = eS j₁ j₂ sp k := by
  rw [eS_eq_getElem _ _ _ k hk]; rfl

theorem eS_zero (j₁ j₂ : V) (sp : List (Finset V)) : eS j₁ j₂ sp 0 = {j₂} := by
  simp [eS, extSpine]

theorem eS_succ (j₁ j₂ : V) (sp : List (Finset V)) (i : ℕ) (hi : i < sp.length) : eS j₁ j₂ sp (i + 1) = sp[i] := by
  simp [eS, extSpine, List.getD_eq_getElem?_getD, List.getElem?_append_left hi, hi]

theorem eS_succ' (j₁ j₂ : V) (sp : List (Finset V)) (i : ℕ) (hi : i + 1 < sp.length) :
    eS j₁ j₂ sp (i + 2) = sp[i + 1] :=
  eS_succ j₁ j₂ sp (i + 1) hi

theorem eS_last (j₁ j₂ : V) (sp : List (Finset V)) : eS j₁ j₂ sp (sp.length + 1) = {j₁} := by
  simp [eS, extSpine, List.getD_eq_getElem?_getD]

/-! ## The layer context -/

/-- **The layer context**: a T-vine with the atom-level spine `sp` and pendant `pd` of N3 Theorem 6 (ii)–(iii) for
the labelling `(j₁, j₂)` (the clauses of `LayervineStructure` used here, verbatim). -/
structure LV (M : Molecule V D) (S : Finset V) (j₁ j₂ : V) (sp pd : List (Finset V)) : Prop where
  tv : TV M S j₁ j₂
  nd : (sp ++ pd).Nodup
  pcs : (sp ++ pd).toFinset = M.pieces S j₁ j₂
  sep : ∀ P ∈ M.pieces S j₁ j₂, P ∈ sp ↔ ¬ ConnIn M (S \ P) j₁ j₂
  ord : ∀ i : Fin sp.length,
    (∀ j : Fin sp.length, j < i → ∀ q ∈ sp.get j, ConnIn M (S \ sp.get i) q j₂) ∧
    (∀ j : Fin sp.length, i < j → ∀ q ∈ sp.get j, ConnIn M (S \ sp.get i) q j₁)
  cons : ∀ i j : Fin (extSpine j₁ j₂ sp).length, i.val + 1 = j.val →
    crossBonds M ((extSpine j₁ j₂ sp).get i) ((extSpine j₁ j₂ sp).get j) = 1 ∨
      crossBonds M ((extSpine j₁ j₂ sp).get i) ((extSpine j₁ j₂ sp).get j) = 2
  non : ∀ i j : Fin (extSpine j₁ j₂ sp).length, i.val + 2 ≤ j.val →
    crossBonds M ((extSpine j₁ j₂ sp).get i) ((extSpine j₁ j₂ sp).get j) = 0

namespace LV

variable {M : Molecule V D} {S : Finset V} {j₁ j₂ : V} {sp pd : List (Finset V)}

theorem mem_pieces (L : LV M S j₁ j₂ sp pd) {P : Finset V} (h : P ∈ sp ∨ P ∈ pd) : P ∈ M.pieces S j₁ j₂ := by
  rw [← L.pcs, List.mem_toFinset, List.mem_append]; exact h

theorem of_pieces (L : LV M S j₁ j₂ sp pd) {P : Finset V} (h : P ∈ M.pieces S j₁ j₂) : P ∈ sp ∨ P ∈ pd := by
  rw [← L.pcs, List.mem_toFinset, List.mem_append] at h; exact h

theorem sp_piece (L : LV M S j₁ j₂ sp pd) (i : ℕ) (hi : i < sp.length) : sp[i] ∈ M.pieces S j₁ j₂ :=
  L.mem_pieces (Or.inl (List.getElem_mem hi))

theorem pw (L : LV M S j₁ j₂ sp pd) : (sp ++ pd).Pairwise (fun A B => Disjoint A B) :=
  L.nd.pairwise_of_forall_ne fun A hA B hB hAB => by
    rw [List.mem_append] at hA hB
    exact piece_disj (L.mem_pieces hA) (L.mem_pieces hB) hAB

theorem sp_pw (L : LV M S j₁ j₂ sp pd) : sp.Pairwise (fun A B => Disjoint A B) :=
  L.pw.sublist (List.sublist_append_left sp pd)

theorem pd_pw (L : LV M S j₁ j₂ sp pd) : pd.Pairwise (fun A B => Disjoint A B) :=
  L.pw.sublist (List.sublist_append_right sp pd)

theorem sp_pd_disj (L : LV M S j₁ j₂ sp pd) : ∀ A ∈ sp, ∀ B ∈ pd, Disjoint A B :=
  (List.pairwise_append.mp L.pw).2.2

theorem sp_pd_ne (L : LV M S j₁ j₂ sp pd) : ∀ A ∈ sp, ∀ B ∈ pd, A ≠ B :=
  (List.pairwise_append.mp (show (sp ++ pd).Pairwise (fun A B : Finset V => A ≠ B) from L.nd)).2.2

theorem sp_nodup (L : LV M S j₁ j₂ sp pd) : sp.Nodup := List.Nodup.sublist (List.sublist_append_left sp pd) L.nd

theorem sp_inj (L : LV M S j₁ j₂ sp pd) {i j : ℕ} {hi : i < sp.length} {hj : j < sp.length}
    (h : sp[i] = sp[j]) : i = j :=
  (List.Nodup.getElem_inj_iff L.sp_nodup).mp h

theorem sp_disj (L : LV M S j₁ j₂ sp pd) {i j : ℕ} (hi : i < sp.length) (hj : j < sp.length) (hij : i ≠ j) :
    Disjoint sp[i] sp[j] :=
  piece_disj (L.sp_piece i hi) (L.sp_piece j hj) (fun h => hij (L.sp_inj h))

theorem sub_S (L : LV M S j₁ j₂ sp pd) {P : Finset V} (h : P ∈ sp ∨ P ∈ pd) : P ⊆ S :=
  (piece_facts (L.mem_pieces h)).1

theorem cover (L : LV M S j₁ j₂ sp pd) :
    ∀ w ∈ S, w = j₁ ∨ w = j₂ ∨ w ∈ unionAll sp ∨ w ∈ unionAll pd := by
  intro w hw
  by_cases h1 : w = j₁
  · exact Or.inl h1
  by_cases h2 : w = j₂
  · exact Or.inr (Or.inl h2)
  obtain ⟨P, hP, hwP⟩ := exists_piece (M := M) hw h1 h2
  rcases L.of_pieces hP with hsp | hpd
  · exact Or.inr (Or.inr (Or.inl (mem_unionAll.mpr ⟨P, hsp, hwP⟩)))
  · exact Or.inr (Or.inr (Or.inr (mem_unionAll.mpr ⟨P, hpd, hwP⟩)))

theorem loc (L : LV M S j₁ j₂ sp pd) :
    ∀ w ∈ S, w ∈ unionAll pd ∨ ∃ k < sp.length + 2, w ∈ eS j₁ j₂ sp k := by
  intro w hw
  rcases L.cover w hw with h | h | h | h
  · exact Or.inr ⟨sp.length + 1, by omega, by rw [eS_last, h]; exact Finset.mem_singleton_self _⟩
  · exact Or.inr ⟨0, by omega, by rw [eS_zero, h]; exact Finset.mem_singleton_self _⟩
  · obtain ⟨P, hP, hwP⟩ := mem_unionAll.mp h
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hP
    exact Or.inr ⟨i + 1, by omega, by rw [eS_succ _ _ _ i hi]; exact hwP⟩
  · exact Or.inl h

theorem cons' (L : LV M S j₁ j₂ sp pd) (k : ℕ) (hk : k + 1 < sp.length + 2) :
    crossBonds M (eS j₁ j₂ sp k) (eS j₁ j₂ sp (k + 1)) = 1 ∨
      crossBonds M (eS j₁ j₂ sp k) (eS j₁ j₂ sp (k + 1)) = 2 := by
  have hl := extSpine_length j₁ j₂ sp
  have := L.cons ⟨k, by omega⟩ ⟨k + 1, by omega⟩ rfl
  rwa [get_extSpine, get_extSpine] at this

theorem cons_le (L : LV M S j₁ j₂ sp pd) (k : ℕ) (hk : k + 1 < sp.length + 2) :
    crossBonds M (eS j₁ j₂ sp k) (eS j₁ j₂ sp (k + 1)) ≤ 2 := by
  rcases L.cons' k hk with h | h <;> omega

theorem non' (L : LV M S j₁ j₂ sp pd) (k l : ℕ) (hl : l < sp.length + 2) (hkl : k + 2 ≤ l) :
    crossBonds M (eS j₁ j₂ sp k) (eS j₁ j₂ sp l) = 0 := by
  have hlen := extSpine_length j₁ j₂ sp
  have := L.non ⟨k, by omega⟩ ⟨l, by omega⟩ hkl
  rwa [get_extSpine, get_extSpine] at this

theorem ext_pw (L : LV M S j₁ j₂ sp pd) : (extSpine j₁ j₂ sp).Pairwise (fun A B => Disjoint A B) := by
  unfold extSpine
  rw [List.pairwise_cons, List.pairwise_append]
  refine ⟨fun B hB => ?_, L.sp_pw, List.pairwise_singleton _ _, fun A hA B hB => ?_⟩
  · rw [List.mem_append, List.mem_singleton] at hB
    rcases hB with hB | rfl
    · exact Finset.disjoint_singleton_left.mpr (piece_facts (L.mem_pieces (Or.inl hB))).2.2.1
    · exact Finset.disjoint_singleton.mpr L.tv.ne.symm
  · rw [List.mem_singleton] at hB
    subst hB
    exact Finset.disjoint_singleton_right.mpr (piece_facts (L.mem_pieces (Or.inl hA))).2.1

theorem eS_disj (L : LV M S j₁ j₂ sp pd) {k l : ℕ} (hkl : k ≠ l) (hk : k < sp.length + 2) (hl : l < sp.length + 2) :
    Disjoint (eS j₁ j₂ sp k) (eS j₁ j₂ sp l) := by
  have hlen := extSpine_length j₁ j₂ sp
  rw [eS_eq_getElem _ _ _ k (by omega), eS_eq_getElem _ _ _ l (by omega)]
  rcases Nat.lt_or_gt_of_ne hkl with h | h
  · exact List.pairwise_iff_getElem.mp L.ext_pw k l (by omega) (by omega) h
  · exact (List.pairwise_iff_getElem.mp L.ext_pw l k (by omega) (by omega) h).symm

/-! ## Bonds at a spine piece -/

/-- Every bond leaving the spine piece `G_i` goes to a neighbour in the extended spine or to the pendant. -/
theorem spine_bound (L : LV M S j₁ j₂ sp pd) (i : ℕ) (hi : i < sp.length) :
    crossBonds M sp[i] (S \ sp[i]) ≤ crossBonds M (eS j₁ j₂ sp i) sp[i] +
      crossBonds M sp[i] (eS j₁ j₂ sp (i + 2)) + crossBonds M sp[i] (unionAll pd) := by
  have hPe : eS j₁ j₂ sp (i + 1) = sp[i] := eS_succ j₁ j₂ sp i hi
  have hsub : bondSet M sp[i] (S \ sp[i]) ⊆ bondSet M (eS j₁ j₂ sp i) sp[i] ∪
      bondSet M sp[i] (eS j₁ j₂ sp (i + 2)) ∪ bondSet M sp[i] (unionAll pd) := by
    intro g hg
    obtain ⟨hgB, hends⟩ := mem_bondSet.mp hg
    have loc : ∀ w ∈ S, w ∉ sp[i] → g ∈ bondSet M sp[i] {w} →
        w ∈ unionAll pd ∨ w ∈ eS j₁ j₂ sp i ∨ w ∈ eS j₁ j₂ sp (i + 2) := by
      intro w hwS hwP hgw
      rcases L.loc w hwS with hH | ⟨k, hk, hwk⟩
      · exact Or.inl hH
      · right
        have hgk : g ∈ bondSet M sp[i] (eS j₁ j₂ sp k) :=
          bondSet_mono subset_rfl (Finset.singleton_subset_iff.mpr hwk) hgw
        rcases lt_trichotomy k (i + 1) with hlt | heq | hgt
        · by_cases hki : k = i
          · subst hki; exact Or.inl hwk
          · exfalso
            have h0 := L.non' k (i + 1) (by omega) (by omega)
            rw [hPe] at h0
            exact not_mem_bondSet_of_zero h0 (by rw [bondSet_comm]; exact hgk)
        · exfalso; subst heq; rw [hPe] at hwk; exact hwP hwk
        · by_cases hki : k = i + 2
          · subst hki; exact Or.inr hwk
          · exfalso
            have h0 := L.non' (i + 1) k hk (by omega)
            rw [hPe] at h0
            exact not_mem_bondSet_of_zero h0 hgk
    have hfin : ∀ w ∈ S, w ∉ sp[i] → g ∈ bondSet M sp[i] {w} →
        g ∈ bondSet M (eS j₁ j₂ sp i) sp[i] ∪ bondSet M sp[i] (eS j₁ j₂ sp (i + 2)) ∪
          bondSet M sp[i] (unionAll pd) := by
      intro w hwS hwP hgw
      rcases loc w hwS hwP hgw with h | h | h
      · exact Finset.mem_union_right _ (bondSet_mono subset_rfl (Finset.singleton_subset_iff.mpr h) hgw)
      · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
        rw [bondSet_comm]
        exact bondSet_mono subset_rfl (Finset.singleton_subset_iff.mpr h) hgw
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (bondSet_mono subset_rfl (Finset.singleton_subset_iff.mpr h) hgw))
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hfin _ (Finset.mem_sdiff.mp h2).1 (Finset.mem_sdiff.mp h2).2
        (mem_bondSet.mpr ⟨hgB, Or.inl ⟨h1, Finset.mem_singleton_self _⟩⟩)
    · exact hfin _ (Finset.mem_sdiff.mp h1).1 (Finset.mem_sdiff.mp h1).2
        (mem_bondSet.mpr ⟨hgB, Or.inr ⟨Finset.mem_singleton_self _, h2⟩⟩)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (bondSet M (eS j₁ j₂ sp i) sp[i] ∪ bondSet M sp[i] (eS j₁ j₂ sp (i + 2)))
    (bondSet M sp[i] (unionAll pd))
  have h3 := Finset.card_union_le (bondSet M (eS j₁ j₂ sp i) sp[i]) (bondSet M sp[i] (eS j₁ j₂ sp (i + 2)))
  simp only [card_bondSet] at h1 h2 h3
  omega

/-- A rung spine piece without pendant bonds is joined to both neighbours by `2` bonds. -/
theorem rung_neighbors (L : LV M S j₁ j₂ sp pd) (i : ℕ) (hi : i < sp.length) (hr : IsRungPiece M sp[i])
    (hH : crossBonds M sp[i] (unionAll pd) = 0) :
    crossBonds M (eS j₁ j₂ sp i) sp[i] = 2 ∧ crossBonds M sp[i] (eS j₁ j₂ sp (i + 2)) = 2 := by
  have h4 := L.tv.rung_cut (L.sp_piece i hi) hr
  have hb := L.spine_bound i hi
  have c1 := L.cons_le i (by omega)
  have c2 : crossBonds M (eS j₁ j₂ sp (i + 1)) (eS j₁ j₂ sp (i + 2)) ≤ 2 := L.cons_le (i + 1) (by omega)
  rw [eS_succ j₁ j₂ sp i hi] at c1 c2
  omega

/-- A junction spine piece (cut `6`) receives at least two bonds of the pendant. -/
theorem junction_H (L : LV M S j₁ j₂ sp pd) (i : ℕ) (hi : i < sp.length) (hj : IsJunctionPiece M sp[i]) :
    2 ≤ crossBonds M sp[i] (unionAll pd) := by
  have h6 := L.tv.junction_cut (L.sp_piece i hi) hj
  have hb := L.spine_bound i hi
  have c1 := L.cons_le i (by omega)
  have c2 : crossBonds M (eS j₁ j₂ sp (i + 1)) (eS j₁ j₂ sp (i + 2)) ≤ 2 := L.cons_le (i + 1) (by omega)
  rw [eS_succ j₁ j₂ sp i hi] at c1 c2
  omega

/-! ## Ladder steps on the spine -/

/-- The bonds leaving a component of `A ⊆ S` (the atoms joined to `T` inside `A`) all end outside `A`. -/
theorem conn_closed {S A Z : Finset V} {T : V} (hZ : ∀ w, w ∈ Z ↔ w ∈ A ∧ ConnIn M A w T) :
    bondSet M Z (S \ Z) ⊆ bondSet M Z (S \ A) := by
  intro g hg
  rw [mem_bondSet] at hg ⊢
  obtain ⟨hgB, h⟩ := hg
  refine ⟨hgB, ?_⟩
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine ⟨h1, Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp h2).1, fun hA' => (Finset.mem_sdiff.mp h2).2
      ((hZ _).mpr ⟨hA', ?_⟩)⟩⟩
    have hz := (hZ _).mp h1
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨g, And.intro hz.1 hA', rfl, rfl⟩)) hz.2
  · right
    refine ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp h1).1, fun hA' => (Finset.mem_sdiff.mp h1).2
      ((hZ _).mpr ⟨hA', ?_⟩)⟩, h2⟩
    have hz := (hZ _).mp h2
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨g, And.intro hA' hz.1, rfl, rfl⟩) hz.2

/-- **Ladder step on the spine** (N3 L295–L296): two consecutive spine pieces, the first a rung piece, joined by
`2` bonds. -/
theorem spine_step (L : LV M S j₁ j₂ sp pd) (i : ℕ) (hi : i + 1 < sp.length)
    (hR : IsRungPiece M (sp[i]'(by omega))) (h2 : crossBonds M (sp[i]'(by omega)) sp[i + 1] = 2) :
    MatchStep M (sp[i]'(by omega)) sp[i + 1] := by
  classical
  have hi' : i < sp.length := by omega
  have hP := L.sp_piece i hi'
  have hQ := L.sp_piece (i + 1) hi
  obtain ⟨hPS, hP1, hP2, -⟩ := piece_facts hP
  obtain ⟨hQS, hQ1, hQ2, ⟨q₀, hq₀⟩⟩ := piece_facts hQ
  have hPQ : Disjoint sp[i] sp[i + 1] := L.sp_disj hi' hi (by omega)
  have hlater : ∀ q ∈ sp[i + 1], ConnIn M (S \ sp[i]) q j₁ := by
    have := (L.ord ⟨i, hi'⟩).2 ⟨i + 1, hi⟩ (Fin.mk_lt_mk.mpr (by omega))
    simpa using this
  have hnot : ¬ ConnIn M (S \ sp[i]) j₁ j₂ := (L.sep _ hP).mp (List.getElem_mem hi')
  set C := (S \ sp[i]).filter fun w => ConnIn M (S \ sp[i]) w j₁ with hCdef
  set Dd := (S \ sp[i]).filter fun w => ConnIn M (S \ sp[i]) w j₂ with hDdef
  have hC : ∀ w, w ∈ C ↔ w ∈ S \ sp[i] ∧ ConnIn M (S \ sp[i]) w j₁ := fun w => Finset.mem_filter
  have hD : ∀ w, w ∈ Dd ↔ w ∈ S \ sp[i] ∧ ConnIn M (S \ sp[i]) w j₂ := fun w => Finset.mem_filter
  have hCA : C ⊆ S \ sp[i] := Finset.filter_subset _ _
  have hDA : Dd ⊆ S \ sp[i] := Finset.filter_subset _ _
  have hSA : S \ (S \ sp[i]) = sp[i] := Finset.sdiff_sdiff_eq_self hPS
  have hCD : Disjoint C Dd := by
    rw [Finset.disjoint_left]
    intro w hwC hwD
    exact hnot (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ ((hC w).mp hwC).2) ((hD w).mp hwD).2)
  have hQC : sp[i + 1] ⊆ C := fun q hq =>
    (hC q).mpr ⟨Finset.mem_sdiff.mpr ⟨hQS hq, Finset.disjoint_right.mp hPQ hq⟩, hlater q hq⟩
  have hj₂D : j₂ ∈ Dd := (hD _).mpr ⟨Finset.mem_sdiff.mpr ⟨L.tv.j₂_mem, hP2⟩, Relation.EqvGen.refl _⟩
  have hj₂C : j₂ ∉ C := fun h => Finset.disjoint_left.mp hCD h hj₂D
  obtain ⟨a, b, hab, hPeq, -⟩ := id hR
  have haP : a ∈ sp[i] := by rw [hPeq]; simp
  have haD : a ∉ Dd := fun h => (Finset.mem_sdiff.mp (hDA h)).2 haP
  -- the cuts
  have hcC : crossBonds M C (S \ C) ≤ crossBonds M C sp[i] := by
    have := conn_closed (S := S) hC
    rw [hSA] at this
    exact Finset.card_le_card this
  have hsum : crossBonds M C sp[i] + crossBonds M Dd sp[i] ≤ crossBonds M sp[i] (S \ sp[i]) := by
    have hdisj : Disjoint (bondSet M C sp[i]) (bondSet M Dd sp[i]) := by
      rw [Finset.disjoint_left]
      intro g h1 h2
      rw [mem_bondSet] at h1 h2
      rcases h1.2 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases h2.2 with ⟨b1, b2⟩ | ⟨b1, b2⟩
      · exact Finset.disjoint_left.mp hCD a1 b1
      · exact (Finset.mem_sdiff.mp (hCA a1)).2 b1
      · exact (Finset.mem_sdiff.mp (hDA b1)).2 a1
      · exact Finset.disjoint_left.mp hCD a2 b2
    have hsub : bondSet M C sp[i] ∪ bondSet M Dd sp[i] ⊆ bondSet M sp[i] (S \ sp[i]) := by
      intro g hg
      rw [Finset.mem_union] at hg
      rw [bondSet_comm]
      rcases hg with hg | hg
      · exact bondSet_mono hCA subset_rfl hg
      · exact bondSet_mono hDA subset_rfl hg
    have hle := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at hle
    exact hle
  have hcD : crossBonds M Dd (S \ Dd) ≤ crossBonds M Dd sp[i] := by
    have := conn_closed (S := S) hD
    rw [hSA] at this
    exact Finset.card_le_card this
  have h4 := L.tv.rung_cut hP hR
  have hD2 : 2 ≤ crossBonds M Dd (S \ Dd) := L.tv.two_le (hDA.trans Finset.sdiff_subset) hj₂D (hPS haP) haD
  have hC2 : 2 ≤ crossBonds M C (S \ C) :=
    L.tv.two_le (hCA.trans Finset.sdiff_subset) (hQC hq₀) L.tv.j₂_mem hj₂C
  have hcut : crossBonds M C (S \ C) = 2 := by omega
  refine L.tv.matchStep_of_cut (hCA.trans Finset.sdiff_subset) hcut ?_ hQC ?_ ?_ (rung_card hR) h2
  · intro w hw
    exact Finset.mem_sdiff.mpr ⟨hPS hw, fun h => (Finset.mem_sdiff.mp (hCA h)).2 hw⟩
  · intro w hw; exact ⟨fun h => hP1 (h ▸ hw), fun h => hP2 (h ▸ hw)⟩
  · intro w hw; exact ⟨fun h => hQ1 (h ▸ hw), fun h => hQ2 (h ▸ hw)⟩

/-- **Ladder step in the pendant**: consecutive pendant pieces, the first a rung piece, joined by `2` bonds; the cut
is `H_{k+1} = Y_{k+1} ∪ ⋯ ∪ Y_s`. -/
theorem pend_step (L : LV M S j₁ j₂ sp pd)
    (hcutk : ∀ k (_hk : k < pd.length),
      crossBonds M (unionAll (pd.drop k)) (S \ unionAll (pd.drop k)) = 2)
    (k : ℕ) (hk : k + 1 < pd.length) (hR : IsRungPiece M (pd[k]'(by omega)))
    (h2 : crossBonds M (pd[k]'(by omega)) pd[k + 1] = 2) : MatchStep M (pd[k]'(by omega)) pd[k + 1] := by
  have hk' : k < pd.length := by omega
  have hP := L.mem_pieces (Or.inr (List.getElem_mem hk'))
  have hQ := L.mem_pieces (Or.inr (List.getElem_mem hk))
  obtain ⟨hPS, hP1, hP2, -⟩ := piece_facts hP
  obtain ⟨hQS, hQ1, hQ2, -⟩ := piece_facts hQ
  have hXS : unionAll (pd.drop (k + 1)) ⊆ S :=
    unionAll_subset fun B hB => L.sub_S (Or.inr (List.mem_of_mem_drop hB))
  refine L.tv.matchStep_of_cut hXS (hcutk (k + 1) hk) ?_ ?_ ?_ ?_ (rung_card hR) h2
  · intro w hw
    refine Finset.mem_sdiff.mpr ⟨hPS hw, fun hwX => ?_⟩
    obtain ⟨B, hB, hwB⟩ := mem_unionAll.mp hwX
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hB
    rw [List.getElem_drop] at hwB
    simp only [List.length_drop] at hj
    have hd := List.pairwise_iff_getElem.mp L.pd_pw k (k + 1 + j) hk' (by omega) (by omega)
    exact Finset.disjoint_left.mp hd hw hwB
  · exact subset_unionAll (List.mem_iff_getElem.mpr ⟨0, by simp; omega, by simp⟩)
  · intro w hw; exact ⟨fun h => hP1 (h ▸ hw), fun h => hP2 (h ▸ hw)⟩
  · intro w hw; exact ⟨fun h => hQ1 (h ▸ hw), fun h => hQ2 (h ▸ hw)⟩

/-- **A slice of the spine** of rung pieces joined by `2` bonds is a run. -/
theorem run_slice (L : LV M S j₁ j₂ sp pd) (o n : ℕ) (hon : o + n ≤ sp.length)
    (hrung : ∀ t (_ht : t < n), IsRungPiece M (sp[o + t]'(by omega)))
    (hcb : ∀ t (_ht : t + 1 < n), crossBonds M (sp[o + t]'(by omega)) (sp[o + t + 1]'(by omega)) = 2)
    (l : List (Finset V)) (hl : l.length = n)
    (hget : ∀ t (_ht : t < n), l[t]'(by omega) = sp[o + t]'(by omega))
    (hpw : l.Pairwise (fun A B => Disjoint A B)) : IsRun M l := by
  refine ⟨fun P hP => ?_, hpw, fun t ht => ?_⟩
  · obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hP
    rw [hget t (by omega)]
    exact hrung t (by omega)
  · rw [hget t (by omega), hget (t + 1) (by omega)]
    have h3 : sp[o + (t + 1)]'(by omega) = sp[o + t + 1]'(by omega) := by simp only [Nat.add_assoc]
    rw [h3]
    exact L.spine_step (o + t) (by omega) (hrung t (by omega)) (hcb t (by omega))

theorem take_drop_disj (L : LV M S j₁ j₂ sp pd) (c d : ℕ) (hcd : c ≤ d) :
    Disjoint (unionAll (sp.take c)) (unionAll (sp.drop d)) := by
  apply disjoint_unionAll
  intro A hA B hB
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hA
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hB
  simp only [List.length_take, List.length_drop] at hi hj
  simp only [List.getElem_take, List.getElem_drop]
  exact L.sp_disj (by omega) (by omega) (by omega)

/-- Splitting the spine at one non-rung piece `G_c`. -/
theorem split_one (L : LV M S j₁ j₂ sp pd) (c : ℕ) (hc : c < sp.length)
    (hrung : ∀ t (ht : t < sp.length), t ≠ c → IsRungPiece M sp[t])
    (hcb : ∀ t (ht : t + 1 < sp.length), crossBonds M (sp[t]'(by omega)) sp[t + 1] = 2) :
    IsRun M (sp.take c) ∧ IsRun M (sp.drop (c + 1)) ∧
      ∀ w ∈ unionAll sp, w ∈ unionAll (sp.take c) ∨ w ∈ sp[c] ∨ w ∈ unionAll (sp.drop (c + 1)) := by
  refine ⟨L.run_slice 0 c (by omega) (fun t ht => by simpa using hrung t (by omega) (by omega))
      (fun t ht => by simpa using hcb t (by omega)) (sp.take c) (by simp; omega) (fun t ht => by simp)
      (L.sp_pw.sublist (List.take_sublist _ _)),
    L.run_slice (c + 1) (sp.length - (c + 1)) (by omega) (fun t ht => hrung (c + 1 + t) _ (by omega))
      (fun t ht => hcb (c + 1 + t) _) (sp.drop (c + 1)) (by simp) (fun t ht => by simp)
      (L.sp_pw.sublist (List.drop_sublist _ _)), ?_⟩
  intro w hw
  have e : sp = sp.take c ++ (sp[c] :: sp.drop (c + 1)) := by
    rw [← List.drop_eq_getElem_cons hc, List.take_append_drop]
  rw [e, unionAll_append', unionAll_cons'] at hw
  simp only [Finset.mem_union] at hw
  tauto

/-- Splitting the spine (all rung pieces) at one consecutive pair `(G_{d-1}, G_d)`. -/
theorem split_two (L : LV M S j₁ j₂ sp pd) (d : ℕ) (hd : d ≤ sp.length)
    (hrung : ∀ t (ht : t < sp.length), IsRungPiece M sp[t])
    (hcb : ∀ t (ht : t + 1 < sp.length), t + 1 ≠ d → crossBonds M (sp[t]'(by omega)) sp[t + 1] = 2) :
    IsRun M (sp.take d) ∧ IsRun M (sp.drop d) ∧
      ∀ w ∈ unionAll sp, w ∈ unionAll (sp.take d) ∨ w ∈ unionAll (sp.drop d) := by
  refine ⟨L.run_slice 0 d (by omega) (fun t ht => by simpa using hrung t (by omega))
      (fun t ht => by simpa using hcb t (by omega) (by omega)) (sp.take d) (by simp; omega)
      (fun t ht => by simp) (L.sp_pw.sublist (List.take_sublist _ _)),
    L.run_slice d (sp.length - d) (by omega) (fun t ht => hrung (d + t) _)
      (fun t ht => hcb (d + t) _ (by omega)) (sp.drop d) (by simp) (fun t ht => by simp)
      (L.sp_pw.sublist (List.drop_sublist _ _)), ?_⟩
  intro w hw
  rw [← List.take_append_drop d sp, unionAll_append'] at hw
  exact Finset.mem_union.mp hw

end LV

/-! ## Bonds of the pendant -/

/-- A set `P` outside the pendant `H` receives at most one bond of `H` per outer end `x`, `x'` it contains. -/
theorem exits_bound {M : Molecule V D} {S H P : Finset V} (hcut : crossBonds M H (S \ H) = 2) {x x' y y' : V}
    (hxx' : x ≠ x') (hx : x ∈ S \ H) (hx' : x' ∈ S \ H) (hy : y ∈ H) (hy' : y' ∈ H)
    (hxy : M.bondsBetween x y = 1) (hx'y' : M.bondsBetween x' y' = 1) (hP : P ⊆ S \ H) :
    crossBonds M P H ≤ (if x ∈ P then 1 else 0) + (if x' ∈ P then 1 else 0) := by
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp
    (show (M.bonds.filter fun z => M.ends z = s(x, y)).card = 1 from hxy)
  obtain ⟨f, hf⟩ := Finset.card_eq_one.mp
    (show (M.bonds.filter fun z => M.ends z = s(x', y')).card = 1 from hx'y')
  have he' : e ∈ M.bonds ∧ M.ends e = s(x, y) :=
    Finset.mem_filter.mp (by rw [he]; exact Finset.mem_singleton_self e)
  have hf' : f ∈ M.bonds ∧ M.ends f = s(x', y') :=
    Finset.mem_filter.mp (by rw [hf]; exact Finset.mem_singleton_self f)
  have hcross : ∀ g ∈ M.bonds, ∀ p q, M.ends g = s(p, q) → p ∈ S \ H → q ∈ H → g ∈ bondSet M H (S \ H) := by
    intro g hg p q hge hp hq
    rw [mem_bondSet]
    refine ⟨hg, ?_⟩
    simp only [Molecule.ends, Sym2.eq_iff] at hge
    rcases hge with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; rw [h1, h2]; exact ⟨hp, hq⟩
    · left; rw [h1, h2]; exact ⟨hq, hp⟩
  have heK := hcross e he'.1 x y he'.2 hx hy
  have hfK := hcross f hf'.1 x' y' hf'.2 hx' hy'
  have hef : e ≠ f := by
    intro hh
    have h1 := he'.2
    rw [hh, hf'.2, Sym2.eq_iff] at h1
    rcases h1 with ⟨h2, -⟩ | ⟨h2, -⟩
    · exact hxx' h2.symm
    · exact (Finset.mem_sdiff.mp hx').2 (h2 ▸ hy)
  have hK : bondSet M H (S \ H) = {e, f} := by
    refine (Finset.eq_of_subset_of_card_le ?_ (by rw [card_bondSet, hcut, Finset.card_pair hef])).symm
    intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl
    · exact heK
    · exact hfK
  have hsub : bondSet M P H ⊆ {e, f} := by
    rw [← hK, bondSet_comm]
    exact bondSet_mono subset_rfl hP
  have hPend : ∀ g ∈ bondSet M P H, ∀ p q, M.ends g = s(p, q) → q ∈ H → p ∈ P := by
    intro g hg p q hge hq
    rw [mem_bondSet] at hg
    simp only [Molecule.ends, Sym2.eq_iff] at hge
    rcases hg.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hge with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · rwa [a1] at h1
    · rw [a1] at h1; exact absurd hq (Finset.mem_sdiff.mp (hP h1)).2
    · rw [a2] at h2; exact absurd hq (Finset.mem_sdiff.mp (hP h2)).2
    · rwa [a2] at h2
  have key : bondSet M P H ⊆ (if x ∈ P then {e} else ∅) ∪ (if x' ∈ P then {f} else ∅) := by
    intro g hg
    have hm := hsub hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · have := hPend g hg x y he'.2 hy; simp [this]
    · have := hPend g hg x' y' hf'.2 hy'; simp [this]
  calc crossBonds M P H = (bondSet M P H).card := rfl
    _ ≤ ((if x ∈ P then ({e} : Finset D) else ∅) ∪ (if x' ∈ P then ({f} : Finset D) else ∅)).card :=
      Finset.card_le_card key
    _ ≤ (if x ∈ P then ({e} : Finset D) else ∅).card + (if x' ∈ P then ({f} : Finset D) else ∅).card :=
      Finset.card_union_le _ _
    _ = (if x ∈ P then 1 else 0) + (if x' ∈ P then 1 else 0) := by split_ifs <;> simp

end WaveTurbulence.TVine.Struct.Ladders
