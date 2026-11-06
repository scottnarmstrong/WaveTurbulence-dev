/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamExpandDecomp
public import WaveTurbulenceVineParam.VineParamSlotCapSupport
import Mathlib.Tactic

/-! # Reflection invariance of the untouched bonds of a prefix expansion -/

public section
namespace WaveTurbulence.Vine.Param

theorem filter_erase_of_not {α : Type*} [DecidableEq α] (l : List α) (a : α) (p : α → Bool)
    (h : p a = false) : (l.erase a).filter p = l.filter p := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases hb : b = a
    · subst hb
      simp [h]
    · rw [List.erase_cons_tail (by simpa using hb)]
      cases hpb : p b <;> simp [hpb,ih]

theorem filter_inside_insertRungs (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ) (C : Finset ℕ)
    (hC : ∀ v ∈ C,v < T.n) (hs : s.1.1 ∉ C ∧ s.1.2 ∉ C ∧ s.2.1 ∉ C ∧ s.2.2 ∉ C) :
    (insertRungs T s k).bonds.filter (fun e => decide (e.1 ∈ C ∧ e.2 ∈ C)) =
      T.bonds.filter (fun e => decide (e.1 ∈ C ∧ e.2 ∈ C)) := by
  by_cases hk : k = 0
  · rw [hk,insertRungs_zero]
  · have hu : ∀ v ∈ (List.range k).map (T.n+·),v ∉ C := by
      intro v hv hmem
      obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hv
      have := hC _ hmem; omega
    have hv : ∀ v ∈ (List.range k).map (T.n+k+·),v ∉ C := by
      intro v hv hmem
      obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hv
      have := hC _ hmem; omega
    simp only [insertRungs,hk,ite_false,List.filter_append]
    have r1 : (railBonds s.1.1 ((List.range k).map (T.n+·)) s.1.2).filter
        (fun e => decide (e.1 ∈ C ∧ e.2 ∈ C)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro e he
      have := railBonds_outside_cap C _ _ _ hs.1 hs.2.1 hu e he
      simp [this.1]
    have r2 : (railBonds s.2.1 ((List.range k).map (T.n+k+·)) s.2.2).filter
        (fun e => decide (e.1 ∈ C ∧ e.2 ∈ C)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro e he
      have := railBonds_outside_cap C _ _ _ hs.2.2.1 hs.2.2.2 hv e he
      simp [this.1]
    have r3 : ((List.zip ((List.range k).map (T.n+·)) ((List.range k).map (T.n+k+·))).flatMap
        (fun p => [p,p])).filter (fun e => decide (e.1 ∈ C ∧ e.2 ∈ C)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro e he
      obtain ⟨p,hp,hep⟩ := List.mem_flatMap.mp he
      have hep' : e = p := by simpa using hep
      have hm := List.of_mem_zip hp
      subst hep'
      simp [hu _ hm.1]
    rw [r1,r2,r3]
    simp only [List.append_nil]
    rw [filter_erase_of_not _ _ _ (by simp [hs.2.2.1]),
      filter_erase_of_not _ _ _ (by simp [hs.1])]

theorem fold_filter_inside (xs : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (T : VineTemplate) (C : Finset ℕ)
    (hC : ∀ v ∈ C,v < T.n)
    (hs : ∀ sk ∈ xs,sk.1.1.1 ∉ C ∧ sk.1.1.2 ∉ C ∧ sk.1.2.1 ∉ C ∧ sk.1.2.2 ∉ C) :
    (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).bonds.filter
      (fun e => decide (e.1 ∈ C ∧ e.2 ∈ C)) =
      T.bonds.filter (fun e => decide (e.1 ∈ C ∧ e.2 ∈ C)) := by
  induction xs generalizing T with
  | nil => rfl
  | cons sk xs ih =>
    rw [List.foldl_cons]
    have hC' : ∀ v ∈ C,v < (insertRungs T sk.1 sk.2).n := by
      intro v hv; rw [insertRungs_atoms]; have := hC v hv; omega
    rw [ih _ hC' (fun z hz => hs z (List.mem_cons_of_mem _ hz)),
      filter_inside_insertRungs T sk.1 sk.2 C hC (hs sk List.mem_cons_self)]

theorem reflect_invariant_of_split (ν : ℕ ≃ ℕ) (C : Finset ℕ) (hν : ∀ t ∉ C,ν t = t)
    (l : List (ℕ×ℕ)) (hcross : ∀ e ∈ l,(e.1 ∈ C ↔ e.2 ∈ C))
    (hin : (((l.filter (fun e => decide (e.1 ∈ C ∧ e.2 ∈ C))).map
        (fun e => s(ν e.1,ν e.2)) : List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) =
      (((l.filter (fun e => decide (e.1 ∈ C ∧ e.2 ∈ C))).map (fun e => s(e.1,e.2)) :
        List (Sym2 ℕ)) : Multiset (Sym2 ℕ))) :
    (bondSym l).map (Sym2.map ν) = bondSym l := by
  have hperm := List.filter_append_perm (fun e : ℕ×ℕ => decide (e.1 ∈ C ∧ e.2 ∈ C)) l
  have hb : bondSym l = bondSym (l.filter (fun e => decide (e.1 ∈ C ∧ e.2 ∈ C))) +
      bondSym (l.filter (fun e => !decide (e.1 ∈ C ∧ e.2 ∈ C))) := by
    unfold bondSym
    rw [Multiset.coe_add,← List.map_append,Multiset.coe_eq_coe]
    exact (hperm.symm.map _)
  rw [hb,Multiset.map_add]
  congr 1
  · unfold bondSym
    rw [Multiset.map_coe,List.map_map]
    exact hin
  · unfold bondSym
    rw [Multiset.map_coe,List.map_map]
    apply congrArg
    apply List.map_congr_left
    intro e he
    obtain ⟨hel,hf⟩ := List.mem_filter.mp he
    have hn : ¬(e.1 ∈ C ∧ e.2 ∈ C) := by intro h; simp [h] at hf
    have h1 : e.1 ∉ C := fun h => hn ⟨h,(hcross e hel).mp h⟩
    have h2 : e.2 ∉ C := fun h => hn ⟨(hcross e hel).mpr h,h⟩
    simp [hν _ h1,hν _ h2]

theorem prefix_slots_outside (X : VineType) (ks1 : List ℕ) (m : ℕ)
    (hlen : ks1.length+1+m = X.template.slots.length) :
    let i : Fin X.template.slots.length := ⟨ks1.length,by omega⟩
    ∀ sk ∈ X.template.slots.zip ks1,sk.1.1.1 ∉ slotCap X i ∧ sk.1.1.2 ∉ slotCap X i ∧
      sk.1.2.1 ∉ slotCap X i ∧ sk.1.2.2 ∉ slotCap X i := by
  intro i sk hsk
  have hi : ks1.length < X.template.slots.length := by omega
  have hz1 : X.template.slots.zip ks1 = (X.template.slots.take ks1.length).zip ks1 :=
    zip_take_eq X.template.slots ks1 hi.le
  rw [hz1] at hsk
  have hm := (List.of_mem_zip hsk).1
  obtain ⟨j,hj,hjeq⟩ := List.mem_iff_getElem.mp hm
  have hj' : j < ks1.length := by
    simp only [List.length_take] at hj; omega
  have hne : (⟨j,by omega⟩ : Fin X.template.slots.length) ≠ i := by
    intro h; have := congrArg Fin.val h; simp [i] at this; omega
  have hsk1 : sk.1 = X.template.slots[j]'(by omega) := by
    rw [← hjeq]; simp [List.getElem_take]
  rw [hsk1]
  exact other_slot_outside_cap X i ⟨j,by omega⟩ (Ne.symm hne)

/-- The untouched bonds of a prefix expansion are invariant, as an unordered
multiset, under the cap reflection of the next slot. -/
theorem slot_reflect_R (X : VineType) (ks1 : List ℕ) (m : ℕ)
    (hlen : ks1.length+1+m = X.template.slots.length) :
    let i : Fin X.template.slots.length := ⟨ks1.length,by omega⟩
    let U := prefTemplate X ks1
    let sl := X.template.slots[i.1]
    (bondSym ((U.bonds.erase sl.1).erase sl.2)).map (Sym2.map (slotReflection X i)) =
      bondSym ((U.bonds.erase sl.1).erase sl.2) := by
  intro i U sl
  have hctx := slot_context X ks1 m hlen
  apply reflect_invariant_of_split (slotReflection X i) (slotCap X i)
    (fun t ht => slotReflection_outside_all X i t ht) _ hctx.2.2.2.2
  have hports := slotCap_marked_ports X i
  have hn1 : (decide (sl.1.1 ∈ slotCap X i ∧ sl.1.2 ∈ slotCap X i)) = false := by
    rcases hports with h | h <;> simp [sl,h]
  have hn2 : (decide (sl.2.1 ∈ slotCap X i ∧ sl.2.2 ∈ slotCap X i)) = false := by
    rcases hports with h | h <;> simp [sl,h]
  have hRU : ((U.bonds.erase sl.1).erase sl.2).filter (fun e => decide (e.1 ∈ slotCap X i ∧ e.2 ∈ slotCap X i)) =
      U.bonds.filter (fun e => decide (e.1 ∈ slotCap X i ∧ e.2 ∈ slotCap X i)) := by
    rw [filter_erase_of_not _ _ (fun e : ℕ×ℕ => decide (e.1 ∈ slotCap X i ∧ e.2 ∈ slotCap X i)) hn2,
      filter_erase_of_not _ _ (fun e : ℕ×ℕ => decide (e.1 ∈ slotCap X i ∧ e.2 ∈ slotCap X i)) hn1]
  have hUT : U.bonds.filter (fun e => decide (e.1 ∈ slotCap X i ∧ e.2 ∈ slotCap X i)) =
      X.template.bonds.filter (fun e => decide (e.1 ∈ slotCap X i ∧ e.2 ∈ slotCap X i)) :=
    fold_filter_inside (X.template.slots.zip ks1) X.template (slotCap X i) (slotCap_old X i)
      (prefix_slots_outside X ks1 m hlen)
  rw [hRU,hUT]
  have := slotReflection_internal_bonds X i
  simpa using this

end WaveTurbulence.Vine.Param
