/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Ladders.Spine
import Mathlib.Tactic

/-!
# N3 Theorem 6 (iv): at most three ladders, at most 13 atoms outside (packet L3-LAD)

`ladders_of : LayervineStatement → PieceShapeStatement → LaddersStatement`.

Source: N3 = `research-gamma-half-3/NOTES.txt` L170 (statement), L291–L305 (proof). With the labelling `(j₁, j₂)` of
N3 Theorem 6 (ii)–(iii) (`LayervineStructure M S j₁ j₂`: spine `sp`, pendant `pd`) and the piece shape
(N2 Prop 1.17(b): one 3-atom core, all other pieces 2-atom with multiplicity 1 or 2):

* **(B)/(C) core on the spine, no pendant.** Every other spine piece is a rung piece (a junction piece has cut `6`,
  but only its two spine neighbours, `≤ 2` bonds each, are joined to it), and every consecutive pair of spine pieces
  is joined by `2` bonds (one of the two is a rung piece with cut `4`). The spine splits at the core into two runs.
* **(D) core in the pendant, attachment (P-a).** The junction piece `J` of the attachment is the only non-rung
  spine piece (uniqueness of the cut-`6` piece), no other spine piece receives a pendant bond, so again every
  consecutive pair is joined by `2` bonds; the spine splits at `J` into two runs, the rung pieces `Y₁, …, Y_{s-1}` of
  the pendant form the third run.
* **(D) core in the pendant, attachment (P-b).** No spine piece receives both pendant bonds, so none is a junction
  piece (cut `6 > 2 + 2 + 1`); the spine splits at the unique consecutive pair joined by `1` bond (if any) into two
  runs; the pendant gives the third.

Each run of `≥ 2` pieces is one ladder (`Basic.run_cover`: the ladder steps are `Spine.LV.spine_step`,
`Spine.LV.pend_step`); outside the ladders lie at most `2` joints, the core (`3`), the junction piece (`2`, case
(P-a) only) and `2` atoms per run: `2 + 3 + 2 + 3 · 2 = 13` (N3 L302–L303).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct.Ladders

open Finset

universe u v

section cards

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
  {P : Finset V}

theorem coreBC_card (h : IsCoreBC M P) : P.card = 3 := by
  obtain ⟨x, y, z, hxy, hyz, hxz, rfl, -⟩ := h
  exact Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩

theorem coreD_card (h : IsCoreD M P) : P.card = 3 := by
  obtain ⟨x, y, z, hxy, hyz, hxz, rfl, -⟩ := h
  exact Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩

theorem twoAtom_card (h : TwoAtomPiece M P) : P.card = 2 := by
  obtain ⟨a, b, hab, rfl, -⟩ := h
  exact Finset.card_pair hab

theorem junction_card (h : IsJunctionPiece M P) : P.card = 2 := by
  obtain ⟨a, b, hab, rfl, -⟩ := h
  exact Finset.card_pair hab

theorem isRun_nil (M : Molecule V D) : IsRun M [] :=
  ⟨fun P hP => by simp at hP, List.Pairwise.nil, fun i h => absurd h (by simp)⟩

end cards

/-- **N3 Theorem 6 (iv)** (`LaddersStatement`): a T-vine of a molecule contains at most 3 pairwise disjoint B2
ladders leaving at most 13 of its atoms uncovered. -/
theorem ladders_of (hL : LayervineStatement.{u, v}) (hP : PieceShapeStatement.{u, v}) :
    LaddersStatement.{u, v} := by
  intro V D _ _ _ M hM S j₁ j₂ hT
  have hTV := TV.of hP hM hT
  obtain ⟨sp, pd, hnd, hpcs, hsep, hord, hcons, hnon, hone, -, hpend⟩ := (hL M S j₁ j₂ hT).1
  have L : LV M S j₁ j₂ sp pd := ⟨hTV, hnd, hpcs, hsep, hord, hcons, hnon⟩
  obtain ⟨core, -, -, hrest, -⟩ := hP M S j₁ j₂ hT
  have eq_core : ∀ P ∈ M.pieces S j₁ j₂, P.card = 3 → P = core := by
    intro P hP' h3
    by_contra hne
    have := twoAtom_card (hrest P hP' hne)
    omega
  have shape : ∀ t (ht : t < sp.length), sp[t] ≠ core → IsRungPiece M sp[t] ∨ IsJunctionPiece M sp[t] :=
    fun t ht hne => two_cases (hrest _ (L.sp_piece t ht) hne)
  have hspS : ∀ P ∈ sp, P ⊆ S := fun P hP => L.sub_S (Or.inl hP)
  have hAS : ∀ c, unionAll (sp.take c) ⊆ S := fun c =>
    unionAll_subset fun P hP => hspS P (List.mem_of_mem_take hP)
  have hBS : ∀ c, unionAll (sp.drop c) ⊆ S := fun c =>
    unionAll_subset fun P hP => hspS P (List.mem_of_mem_drop hP)
  rcases hpend with ⟨rfl, P₀, hP₀, hBC⟩ | ⟨Ys, C, rfl, hCD, hYs, hpc, -, hex⟩
  · -- (B)/(C) core on the spine, no pendant
    have hP₀core : P₀ = core := eq_core P₀ (L.mem_pieces (Or.inl hP₀)) (coreBC_card hBC)
    obtain ⟨c, hc, hspc⟩ := List.mem_iff_getElem.mp hP₀
    have hH0 : ∀ t (ht : t < sp.length), crossBonds M sp[t] (unionAll ([] : List (Finset V))) = 0 :=
      fun t ht => by rw [unionAll_nil']; exact crossBonds_empty_right M _
    have hrung : ∀ t (ht : t < sp.length), t ≠ c → IsRungPiece M sp[t] := by
      intro t ht htc
      have hne : sp[t] ≠ core := fun e => htc (L.sp_inj (e.trans (hspc.trans hP₀core).symm))
      rcases shape t ht hne with h | h
      · exact h
      · exfalso
        have := L.junction_H t ht h
        rw [hH0 t ht] at this
        omega
    have hcb : ∀ t (ht : t + 1 < sp.length), crossBonds M (sp[t]'(by omega)) sp[t + 1] = 2 := by
      intro t ht
      by_cases htc : t = c
      · have := (L.rung_neighbors (t + 1) ht (hrung (t + 1) ht (by omega)) (hH0 (t + 1) ht)).1
        rwa [eS_succ j₁ j₂ sp t (by omega)] at this
      · have := (L.rung_neighbors t (by omega) (hrung t (by omega) htc) (hH0 t (by omega))).2
        rwa [eS_succ' j₁ j₂ sp t ht] at this
    obtain ⟨hA, hB, hcovsp⟩ := L.split_one c hc hrung hcb
    refine assemble (X := core) (j₁ := j₁) (j₂ := j₂) hA hB (isRun_nil M) (hAS c) (hBS (c + 1))
      (by simp [unionAll_nil']) (L.take_drop_disj c (c + 1) (by omega)) (by simp [unionAll_nil'])
      (by simp [unionAll_nil']) ?_ (by rw [← hP₀core, coreBC_card hBC]; omega)
    intro w hw
    rcases L.cover w hw with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rcases hcovsp w h with h' | h' | h'
      · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
      · exact Or.inr (Or.inr (Or.inl (by rw [← hP₀core, ← hspc]; exact h')))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
    · simp [unionAll_nil'] at h
  · -- (D) core in the pendant
    have hCmem : C ∈ Ys ++ [C] := by simp
    have hCcore : C = core := eq_core C (L.mem_pieces (Or.inr hCmem)) (coreD_card hCD)
    have hnotcore : ∀ t (ht : t < sp.length), sp[t] ≠ core := fun t ht e =>
      L.sp_pd_ne _ (List.getElem_mem ht) C hCmem (e.trans hCcore.symm)
    have hcutk : ∀ k (_hk : k < (Ys ++ [C]).length),
        crossBonds M (unionAll ((Ys ++ [C]).drop k)) (S \ unionAll ((Ys ++ [C]).drop k)) = 2 := by
      intro k hk
      obtain ⟨x, x', hT2, -⟩ := hex ⟨k, hk⟩
      exact hT2.1
    -- the pendant run `Y₁, …, Y_{s-1}`
    have hYrun : IsRun M Ys := by
      refine ⟨hYs, L.pd_pw.sublist (List.sublist_append_left _ _), fun k hk => ?_⟩
      have hk2 : k + 1 < (Ys ++ [C]).length := by simp; omega
      have e1 : (Ys ++ [C])[k]'(by simp; omega) = Ys[k] := List.getElem_append_left (by omega)
      have e2 : (Ys ++ [C])[k + 1]'hk2 = Ys[k + 1] := List.getElem_append_left hk
      have hR : IsRungPiece M ((Ys ++ [C])[k]'(by simp; omega)) := by
        rw [e1]; exact hYs _ (List.getElem_mem _)
      have h2 : crossBonds M ((Ys ++ [C])[k]'(by simp; omega)) (Ys ++ [C])[k + 1] = 2 := by
        have := hpc ⟨k, by simp; omega⟩ ⟨k + 1, hk2⟩ rfl
        simpa using this
      have := L.pend_step hcutk k hk2 hR h2
      rwa [e1, e2] at this
    -- the exits of the pendant
    obtain ⟨x, x', hT0, hatt⟩ := hex ⟨0, by simp⟩
    have hatt' := hatt rfl
    obtain ⟨hcut0, hxx', hx, hx', y, hy, y', hy', -, hxy, hx'y'⟩ := hT0
    simp only [List.drop_zero] at hcut0 hx hx'
    have hyH : y ∈ unionAll (Ys ++ [C]) := subset_unionAll (List.get_mem _ _) hy
    have hy'H : y' ∈ unionAll (Ys ++ [C]) := subset_unionAll (List.get_mem _ _) hy'
    have hspH : ∀ t (ht : t < sp.length), sp[t] ⊆ S \ unionAll (Ys ++ [C]) := by
      intro t ht w hw
      refine Finset.mem_sdiff.mpr ⟨hspS _ (List.getElem_mem ht) hw, fun hwH => ?_⟩
      obtain ⟨B, hB, hwB⟩ := mem_unionAll.mp hwH
      exact Finset.disjoint_left.mp (L.sp_pd_disj _ (List.getElem_mem ht) B hB) hw hwB
    have hHb : ∀ t (ht : t < sp.length), crossBonds M sp[t] (unionAll (Ys ++ [C])) ≤
        (if x ∈ sp[t] then 1 else 0) + (if x' ∈ sp[t] then 1 else 0) :=
      fun t ht => exits_bound hcut0 hxx' hx hx' hyH hy'H hxy hx'y' (hspH t ht)
    -- disjointness of the spine runs from the pendant run
    have hdY : ∀ l : List (Finset V), (∀ P ∈ l, P ∈ sp) → Disjoint (unionAll l) (unionAll Ys) := by
      intro l hl
      exact disjoint_unionAll fun A hA B hB =>
        L.sp_pd_disj A (hl A hA) B (List.mem_append_left _ hB)
    have hYS : unionAll Ys ⊆ S :=
      unionAll_subset fun P hP => L.sub_S (Or.inr (List.mem_append_left _ hP))
    have hpdcov : ∀ w ∈ unionAll (Ys ++ [C]), w ∈ unionAll Ys ∨ w ∈ C := by
      intro w hw
      rw [unionAll_append', unionAll_cons', unionAll_nil', Finset.union_empty, Finset.mem_union] at hw
      exact hw
    rcases hatt' with ⟨i, hxi, hx'i, hJ, h6, huniq⟩ | ⟨i, j, hij, h1, hxx⟩
    · -- (P-a): both outer ends in the junction piece `J = G_c`
      obtain ⟨c, hc⟩ := i
      simp only [List.get_eq_getElem] at hxi hx'i hJ huniq
      have hrung : ∀ t (ht : t < sp.length), t ≠ c → IsRungPiece M sp[t] := by
        intro t ht htc
        rcases shape t ht (hnotcore t ht) with h | h
        · exact h
        · exfalso
          exact htc (L.sp_inj (huniq _ (L.sp_piece t ht) (L.tv.junction_cut (L.sp_piece t ht) h)))
      have hH0 : ∀ t (ht : t < sp.length), t ≠ c → crossBonds M sp[t] (unionAll (Ys ++ [C])) = 0 := by
        intro t ht htc
        have hd := L.sp_disj ht hc htc
        have hxn : x ∉ sp[t] := fun h => Finset.disjoint_left.mp hd h hxi
        have hx'n : x' ∉ sp[t] := fun h => Finset.disjoint_left.mp hd h hx'i
        have := hHb t ht
        simp only [hxn, hx'n, ite_false] at this
        omega
      have hcb : ∀ t (ht : t + 1 < sp.length), crossBonds M (sp[t]'(by omega)) sp[t + 1] = 2 := by
        intro t ht
        by_cases htc : t = c
        · have := (L.rung_neighbors (t + 1) ht (hrung (t + 1) ht (by omega)) (hH0 (t + 1) ht (by omega))).1
          rwa [eS_succ j₁ j₂ sp t (by omega)] at this
        · have := (L.rung_neighbors t (by omega) (hrung t (by omega) htc) (hH0 t (by omega) htc)).2
          rwa [eS_succ' j₁ j₂ sp t ht] at this
      obtain ⟨hA, hB, hcovsp⟩ := L.split_one c hc hrung hcb
      refine assemble (X := sp[c] ∪ C) (j₁ := j₁) (j₂ := j₂) hA hB hYrun (hAS c) (hBS (c + 1)) hYS
        (L.take_drop_disj c (c + 1) (by omega)) (hdY _ fun P hP => List.mem_of_mem_take hP)
        (hdY _ fun P hP => List.mem_of_mem_drop hP) ?_ ?_
      · intro w hw
        rcases L.cover w hw with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · rcases hcovsp w h with h' | h' | h'
          · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
          · exact Or.inr (Or.inr (Or.inl (Finset.mem_union_left _ h')))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
        · rcases hpdcov w h with h' | h'
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h'))))
          · exact Or.inr (Or.inr (Or.inl (Finset.mem_union_right _ h')))
      · have := Finset.card_union_le sp[c] C
        rw [junction_card hJ, coreD_card hCD] at this
        exact this
    · -- (P-b): the outer ends in two consecutive members joined by one bond
      have hlen := extSpine_length j₁ j₂ sp
      have hiv : i.val < sp.length + 2 := by have := i.isLt; omega
      have hjv : j.val < sp.length + 2 := by have := j.isLt; omega
      rw [show (extSpine j₁ j₂ sp).get i = eS j₁ j₂ sp i.val from get_extSpine _ _ _ i.val i.isLt,
        show (extSpine j₁ j₂ sp).get j = eS j₁ j₂ sp j.val from get_extSpine _ _ _ j.val j.isLt] at hxx
      have hnotboth : ∀ t (ht : t < sp.length), ¬ (x ∈ sp[t] ∧ x' ∈ sp[t]) := by
        rintro t ht ⟨hxt, hx't⟩
        rw [← eS_succ j₁ j₂ sp t ht] at hxt hx't
        have key : ∀ k, k < sp.length + 2 → ∀ z, z ∈ eS j₁ j₂ sp k → z ∈ eS j₁ j₂ sp (t + 1) → k = t + 1 := by
          intro k hk z hzk hzt
          by_contra hne
          exact Finset.disjoint_left.mp (L.eS_disj hne hk (by omega)) hzk hzt
        rcases hxx with ⟨a, b⟩ | ⟨a, b⟩
        · have e1 := key _ hiv x a hxt
          have e2 := key _ hjv x' b hx't
          omega
        · have e1 := key _ hiv x' a hx't
          have e2 := key _ hjv x b hxt
          omega
      have hrung : ∀ t (ht : t < sp.length), IsRungPiece M sp[t] := by
        intro t ht
        rcases shape t ht (hnotcore t ht) with h | h
        · exact h
        · exfalso
          have h2 := L.junction_H t ht h
          have hb := hHb t ht
          by_cases hxt : x ∈ sp[t] <;> by_cases hx't : x' ∈ sp[t]
          · exact hnotboth t ht ⟨hxt, hx't⟩
          · simp only [hxt, hx't, ite_true, ite_false] at hb; omega
          · simp only [hxt, hx't, ite_true, ite_false] at hb; omega
          · simp only [hxt, hx't, ite_false] at hb; omega
      have cb12 : ∀ s (hs : s + 1 < sp.length), crossBonds M (sp[s]'(by omega)) sp[s + 1] = 1 ∨
          crossBonds M (sp[s]'(by omega)) sp[s + 1] = 2 := by
        intro s hs
        have := L.cons' (s + 1) (by omega)
        rwa [eS_succ j₁ j₂ sp s (by omega), eS_succ j₁ j₂ sp (s + 1) hs] at this
      have hone' : ∀ s t (hs : s + 1 < sp.length) (ht : t + 1 < sp.length),
          crossBonds M (sp[s]'(by omega)) sp[s + 1] = 1 → crossBonds M (sp[t]'(by omega)) sp[t + 1] = 1 →
            s = t := by
        intro s t hs ht h₁ h₂
        have := hone ⟨s + 1, by omega⟩ ⟨s + 2, by omega⟩ ⟨t + 1, by omega⟩ ⟨t + 2, by omega⟩ rfl rfl
          (by rw [get_extSpine, get_extSpine, eS_succ j₁ j₂ sp s (by omega), eS_succ' j₁ j₂ sp s hs]; exact h₁)
          (by rw [get_extSpine, get_extSpine, eS_succ j₁ j₂ sp t (by omega), eS_succ' j₁ j₂ sp t ht]; exact h₂)
        have := congrArg Fin.val this
        simp only at this
        omega
      have hsplit : ∃ d ≤ sp.length, ∀ s (hs : s + 1 < sp.length), s + 1 ≠ d →
          crossBonds M (sp[s]'(by omega)) sp[s + 1] = 2 := by
        by_cases hex1 : ∃ t, ∃ ht : t + 1 < sp.length, crossBonds M (sp[t]'(by omega)) sp[t + 1] = 1
        · obtain ⟨t₀, ht₀, h₀⟩ := hex1
          refine ⟨t₀ + 1, by omega, fun s hs hne => ?_⟩
          rcases cb12 s hs with h | h
          · exact absurd (hone' s t₀ hs ht₀ h h₀) (by omega)
          · exact h
        · refine ⟨sp.length, le_refl _, fun s hs _ => ?_⟩
          rcases cb12 s hs with h | h
          · exact absurd ⟨s, hs, h⟩ hex1
          · exact h
      obtain ⟨d, hd, hcb⟩ := hsplit
      obtain ⟨hA, hB, hcovsp⟩ := L.split_two d hd hrung hcb
      refine assemble (X := C) (j₁ := j₁) (j₂ := j₂) hA hB hYrun (hAS d) (hBS d) hYS
        (L.take_drop_disj d d le_rfl) (hdY _ fun P hP => List.mem_of_mem_take hP)
        (hdY _ fun P hP => List.mem_of_mem_drop hP) ?_ (by rw [coreD_card hCD]; omega)
      intro w hw
      rcases L.cover w hw with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · rcases hcovsp w h with h' | h'
        · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
      · rcases hpdcov w h with h' | h'
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h'))))
        · exact Or.inr (Or.inr (Or.inl h'))

end WaveTurbulence.TVine.Struct.Ladders
