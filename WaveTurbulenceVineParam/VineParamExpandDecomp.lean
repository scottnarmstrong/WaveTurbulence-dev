/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCapFold
public import WaveTurbulenceVineParam.VineParamSlotCaps
public import WaveTurbulence.Foundations.Molecule.VineExpansionCounts
public import WaveTurbulenceVineParam.VineParamExpandSym
public import WaveTurbulence.Foundations.Molecule.VineExpansionSequences
public import WaveTurbulence.Foundations.Molecule.VineEndpointBounds
import Mathlib.Tactic

/-! # Decomposing a full expansion at its last nonzero slot -/

public section
namespace WaveTurbulence.Vine.Param

/-- The template after the insertions of the leading slots. -/
@[expose] def prefTemplate (X : VineType) (ks1 : List ℕ) : VineTemplate :=
  (X.template.slots.zip ks1).foldl (fun U sk => insertRungs U sk.1 sk.2) X.template

theorem foldl_zero_tail (l : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (T : VineTemplate)
    (h : ∀ sk ∈ l,sk.2=0) : l.foldl (fun U sk => insertRungs U sk.1 sk.2) T = T := by
  induction l generalizing T with
  | nil => rfl
  | cons sk l ih =>
    rw [List.foldl_cons,h sk List.mem_cons_self,insertRungs_zero]
    exact ih T (fun z hz => h z (List.mem_cons_of_mem _ hz))

theorem expand_decomp (X : VineType) (ks1 : List ℕ) (k m : ℕ)
    (hlen : ks1.length+1+m=X.template.slots.length) :
    X.expand (ks1 ++ k :: List.replicate m 0) =
      insertRungs (prefTemplate X ks1)
        (X.template.slots[ks1.length]'(by omega)) k := by
  have hi : ks1.length < X.template.slots.length := by omega
  unfold VineType.expand prefTemplate
  have hsl : X.template.slots = X.template.slots.take ks1.length ++
      X.template.slots[ks1.length] :: X.template.slots.drop (ks1.length+1) := by
    rw [← List.drop_eq_getElem_cons hi,List.take_append_drop]
  have htk : (X.template.slots.take ks1.length).length = ks1.length := by
    simp [List.length_take]; omega
  have hz : X.template.slots.zip (ks1 ++ k :: List.replicate m 0) =
      (X.template.slots.take ks1.length).zip ks1 ++
        (X.template.slots[ks1.length],k) ::
          (X.template.slots.drop (ks1.length+1)).zip (List.replicate m 0) := by
    conv_lhs => rw [hsl]
    rw [List.zip_append htk]
    rfl
  have hz1 : X.template.slots.zip ks1 = (X.template.slots.take ks1.length).zip ks1 := by
    conv_lhs => rw [hsl]
    have := List.zip_append (r₁ := X.template.slots[ks1.length] ::
      X.template.slots.drop (ks1.length+1)) (r₂ := ([] : List ℕ)) htk
    simpa using this
  rw [hz,List.foldl_append,List.foldl_cons,← hz1]
  rw [foldl_zero_tail]
  intro sk hsk
  obtain ⟨_,hsk2⟩ := List.of_mem_zip hsk
  exact List.eq_of_mem_replicate hsk2

theorem fold_mem_post (xs ys : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (T : VineTemplate)
    (hn : (slotMembers (xs ++ ys)).Nodup) (hm : ∀ e ∈ slotMembers (xs ++ ys),e ∈ T.bonds) :
    ∀ e ∈ slotMembers ys,e ∈ (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).bonds := by
  induction xs generalizing T with
  | nil =>
    intro e he
    exact hm e (by simpa using he)
  | cons sk xs ih =>
    have hsm : slotMembers ((sk :: xs) ++ ys) = sk.1.1 :: sk.1.2 :: slotMembers (xs ++ ys) := by
      simp [slotMembers]
    rw [hsm] at hn hm
    obtain ⟨h1,hn'⟩ := List.nodup_cons.mp hn
    obtain ⟨h2,htail⟩ := List.nodup_cons.mp hn'
    rw [List.foldl_cons]
    apply ih _ htail
    intro e he
    apply mem_insertRungs_bonds (hm e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he)))
    · intro heq; exact h1 (List.mem_cons_of_mem _ (heq ▸ he))
    · intro heq; exact h2 (heq ▸ he)

theorem railBonds_fresh (z z' base k : ℕ) (hk : 0 < k) :
    ∀ p ∈ railBonds z ((List.range k).map (base + ·)) z',base ≤ p.1 ∨ base ≤ p.2 := by
  obtain ⟨k',rfl⟩ : ∃ k',k=k'+1 := ⟨k-1,by omega⟩
  rw [List.range_succ_eq_map]
  simp only [railBonds,List.map_cons,List.map_map,List.cons_append,List.zip_cons_cons]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · right; simp
  · have hh := List.of_mem_zip hp
    left
    rcases List.mem_cons.mp hh.1 with h | h
    · omega
    · obtain ⟨i,_,hi⟩ := List.mem_map.mp h
      rw [← hi]; simp only [Function.comp_apply]; omega

theorem insertRungs_count_old (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ) (e : ℕ×ℕ)
    (he : e.1 < T.n ∧ e.2 < T.n) (h1 : e ≠ s.1) (h2 : e ≠ s.2) :
    (insertRungs T s k).bonds.count e = T.bonds.count e := by
  by_cases hk : k = 0
  · rw [hk,insertRungs_zero]
  · simp only [insertRungs,hk,ite_false,List.count_append]
    have hfr : ∀ (z z' b : ℕ), T.n ≤ b → (∀ p ∈ railBonds z ((List.range k).map (b + ·)) z',
        e ≠ p) := by
      intro z z' b hb p hp hep
      rcases railBonds_fresh z z' b k (by omega) p hp with h | h
      · rw [← hep] at h; omega
      · rw [← hep] at h; omega
    have r1 := List.count_eq_zero.mpr (fun hm => hfr s.1.1 s.1.2 T.n le_rfl e hm rfl)
    have r2 := List.count_eq_zero.mpr (fun hm => hfr s.2.1 s.2.2 (T.n+k) (by omega) e hm rfl)
    have r3 : List.count e ((List.zip ((List.range k).map (T.n + ·)) ((List.range k).map (T.n+k+ ·))).flatMap
        (fun p => [p,p])) = 0 := by
      apply List.count_eq_zero.mpr
      intro hm
      obtain ⟨p,hp,hep⟩ := List.mem_flatMap.mp hm
      have hep' : e = p := by simpa using hep
      have hm' := List.of_mem_zip hp
      obtain ⟨i,_,hi⟩ := List.mem_map.mp hm'.1
      rw [hep'] at he
      simp only [← hi] at he
      omega
    rw [r1,r2,r3,List.count_erase_of_ne h2,List.count_erase_of_ne h1]
    omega

theorem fold_count_old (xs : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (T : VineTemplate) (e : ℕ×ℕ)
    (he : e.1 < T.n ∧ e.2 < T.n) (hne : ∀ sk ∈ xs,e ≠ sk.1.1 ∧ e ≠ sk.1.2) :
    (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).bonds.count e = T.bonds.count e := by
  induction xs generalizing T with
  | nil => rfl
  | cons sk xs ih =>
    rw [List.foldl_cons]
    have hh := hne sk List.mem_cons_self
    have hT : e.1 < (insertRungs T sk.1 sk.2).n ∧ e.2 < (insertRungs T sk.1 sk.2).n := by
      rw [insertRungs_atoms]; omega
    rw [ih _ hT (fun z hz => hne z (List.mem_cons_of_mem _ hz)),
      insertRungs_count_old T sk.1 sk.2 e he hh.1 hh.2]

theorem slots_distinct (X : VineType) : ∀ (i j : Fin X.template.slots.length),i ≠ j →
    X.template.slots[i.1].1 ≠ X.template.slots[j.1].1 ∧ X.template.slots[i.1].1 ≠ X.template.slots[j.1].2 ∧
    X.template.slots[i.1].2 ≠ X.template.slots[j.1].1 ∧ X.template.slots[i.1].2 ≠ X.template.slots[j.1].2 := by
  cases X <;> decide

theorem slot_pair_ne (X : VineType) : ∀ (i : Fin X.template.slots.length),
    X.template.slots[i.1].1 ≠ X.template.slots[i.1].2 := by
  cases X <;> decide

theorem slot_count_one (X : VineType) : ∀ (i : Fin X.template.slots.length),
    X.template.bonds.count X.template.slots[i.1].1 = 1 ∧
      X.template.bonds.count X.template.slots[i.1].2 = 1 := by
  cases X <;> decide

theorem zip_take_eq {α β : Type*} (l : List α) (r : List β) (h : r.length ≤ l.length) :
    l.zip r = (l.take r.length).zip r := by
  induction r generalizing l with
  | nil => simp
  | cons b r ih =>
    cases l with
    | nil => simp at h
    | cons a l =>
      simp only [List.length_cons,Nat.add_le_add_iff_right] at h
      simp [List.zip_cons_cons,ih l h]

theorem slot_context (X : VineType) (ks1 : List ℕ) (m : ℕ)
    (hlen : ks1.length+1+m = X.template.slots.length) :
    let i : Fin X.template.slots.length := ⟨ks1.length,by omega⟩
    let U := prefTemplate X ks1
    let sl := X.template.slots[i.1]
    X.template.n ≤ U.n ∧ sl.1 ∈ U.bonds ∧ sl.2 ∈ U.bonds.erase sl.1 ∧
    (∀ e ∈ (U.bonds.erase sl.1).erase sl.2,e.1 < U.n ∧ e.2 < U.n) ∧
    (∀ e ∈ (U.bonds.erase sl.1).erase sl.2,(e.1 ∈ slotCap X i ↔ e.2 ∈ slotCap X i)) := by
  intro i U sl
  have hi : ks1.length < X.template.slots.length := by omega
  have hz1 : X.template.slots.zip ks1 = (X.template.slots.take ks1.length).zip ks1 := by
    have := zip_take_eq X.template.slots ks1 hi.le
    exact this
  have hxs : ∀ sk ∈ X.template.slots.zip ks1,∃ j : Fin X.template.slots.length,j ≠ i ∧
      sk.1 = X.template.slots[j.1] := by
    intro sk hsk
    rw [hz1] at hsk
    have hm := (List.of_mem_zip hsk).1
    obtain ⟨j,hj,hjeq⟩ := List.mem_iff_getElem.mp hm
    have hj' : j < ks1.length := by
      simp only [List.length_take] at hj; omega
    refine ⟨⟨j,by omega⟩,?_,?_⟩
    · intro h; have := congrArg Fin.val h; simp [i] at this; omega
    · rw [← hjeq]; simp [List.getElem_take]
  have hU : U = (X.template.slots.zip ks1).foldl (fun U sk => insertRungs U sk.1 sk.2) X.template :=
    rfl
  have hends : ∀ sk ∈ X.template.slots.zip ks1,sk.1.1.1 < X.template.n ∧ sk.1.1.2 < X.template.n ∧
      sk.1.2.1 < X.template.n ∧ sk.1.2.2 < X.template.n := by
    intro sk hsk
    exact template_slot_endpoints X sk.1 (List.of_mem_zip hsk).1
  have hUn : U.n = X.template.n + 2*((X.template.slots.zip ks1).map Prod.snd).sum := by
    rw [hU]; exact fold_insertRungs_atoms _ _
  have hUend := fold_insertRungs_endpoints (X.template.slots.zip ks1) X.template
    (template_endpoints X) hends
  -- presence of the slot bonds
  have hpres : sl.1 ∈ U.bonds ∧ sl.2 ∈ U.bonds := by
    have hxy : X.template.slots.zip (ks1 ++ List.replicate (m+1) 0) =
        X.template.slots.zip ks1 ++ (X.template.slots.drop ks1.length).zip (List.replicate (m+1) 0) := by
      have htk : (X.template.slots.take ks1.length).length = ks1.length := by
        simp [List.length_take]; omega
      conv_lhs => rw [← List.take_append_drop ks1.length X.template.slots]
      rw [List.zip_append htk,hz1]
    have hl : (ks1 ++ List.replicate (m+1) 0).length = X.template.slots.length := by
      simp; omega
    have hslots : slotMembers (X.template.slots.zip (ks1 ++ List.replicate (m+1) 0)) =
        X.template.slots.flatMap (fun s => [s.1,s.2]) := by
      conv_rhs => rw [← List.map_fst_zip (l₂ := ks1 ++ List.replicate (m+1) 0) hl.symm.le]
      rw [List.flatMap_map]
      rfl
    have hready := template_slots_ready X
    rw [hxy] at hslots
    have hh := fold_mem_post (X.template.slots.zip ks1)
      ((X.template.slots.drop ks1.length).zip (List.replicate (m+1) 0)) X.template
      (hslots ▸ hready.1) (hslots ▸ hready.2)
    have hd : X.template.slots.drop ks1.length = X.template.slots[ks1.length] ::
        X.template.slots.drop (ks1.length+1) := List.drop_eq_getElem_cons hi
    have hr : List.replicate (m+1) 0 = 0 :: List.replicate m 0 := rfl
    rw [hd,hr] at hh
    constructor
    · exact hh sl.1 (by
        simp only [List.zip_cons_cons,slotMembers,List.flatMap_cons,List.cons_append,
          List.mem_cons,true_or,sl,i])
    · exact hh sl.2 (by
        simp only [List.zip_cons_cons,slotMembers,List.flatMap_cons,List.cons_append,
          List.mem_cons,true_or,or_true,sl,i])
  have hne : sl.2 ≠ sl.1 := (slot_pair_ne X i).symm
  have hsother : ∀ sk ∈ X.template.slots.zip ks1,sk.1.1.1 ∉ slotCap X i ∧ sk.1.1.2 ∉ slotCap X i ∧
      sk.1.2.1 ∉ slotCap X i ∧ sk.1.2.2 ∉ slotCap X i := by
    intro sk hsk
    obtain ⟨j,hj,hsj⟩ := hxs sk hsk
    rw [hsj]
    exact other_slot_outside_cap X i j (Ne.symm hj)
  have hcnt : ∀ (e : ℕ×ℕ),e = sl.1 ∨ e = sl.2 → e.1 < X.template.n ∧ e.2 < X.template.n →
      U.bonds.count e = 1 := by
    intro e he hlt
    have hh := fold_count_old (X.template.slots.zip ks1) X.template e hlt (by
      intro sk hsk
      obtain ⟨j,hj,hsj⟩ := hxs sk hsk
      have hd := slots_distinct X i j (Ne.symm hj)
      rw [hsj]
      rcases he with rfl | rfl
      · exact ⟨hd.1,hd.2.1⟩
      · exact ⟨hd.2.2.1,hd.2.2.2⟩)
    have h1 := slot_count_one X i
    rcases he with rfl | rfl
    · exact hh.trans h1.1
    · exact hh.trans h1.2
  have hslt := template_slot_endpoints X sl (List.getElem_mem _)
  refine ⟨by rw [hUn]; omega,hpres.1,(List.mem_erase_of_ne hne).mpr hpres.2,?_,?_⟩
  · intro e he
    exact hUend e (List.mem_of_mem_erase (List.mem_of_mem_erase he))
  · intro e he
    by_contra hc
    have heU : e ∈ U.bonds := List.mem_of_mem_erase (List.mem_of_mem_erase he)
    have hcap := fold_insertRungs_cap_crossing_old (X.template.slots.zip ks1) X.template
      (slotCap X i) (slotCap_old X i) hsother heU hc
    rcases slotCap_cut X i e hcap with h | h | h
    · exact hc h
    · -- e is the first slot bond, which occurs only once
      subst h
      have hm1 : sl.1 ∈ U.bonds.erase sl.1 := List.mem_of_mem_erase he
      have a2 : U.bonds.count sl.1 = 1 := hcnt sl.1 (Or.inl rfl) ⟨hslt.1,hslt.2.1⟩
      have a1 : (U.bonds.erase sl.1).count sl.1 = U.bonds.count sl.1 - 1 :=
        List.count_erase_self
      have a3 : 0 < (U.bonds.erase sl.1).count sl.1 := List.count_pos_iff.mpr hm1
      omega
    · subst h
      have a2 : U.bonds.count sl.2 = 1 := hcnt sl.2 (Or.inr rfl) ⟨hslt.2.2.1,hslt.2.2.2⟩
      have a3 : (U.bonds.erase sl.1).count sl.2 = 1 := by
        rw [List.count_erase_of_ne hne]; exact a2
      have a4 : ((U.bonds.erase sl.1).erase sl.2).count sl.2 =
          (U.bonds.erase sl.1).count sl.2 - 1 := List.count_erase_self
      have a5 : 0 < ((U.bonds.erase sl.1).erase sl.2).count sl.2 := List.count_pos_iff.mpr he
      omega

end WaveTurbulence.Vine.Param
