/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperCoreCut
public import WaveTurbulence.Foundations.Molecule.VineExpansionSequences
public import WaveTurbulence.Foundations.Molecule.VineZeroSlotBonds
import Mathlib.Tactic

/-! # VINE-RHO (1): slot cuts of expanded vine templates

For each of the 14 slots of the 8 vine templates we fix the side `sideOf X s` of the template atoms
reachable from the slot's starting rails when the two slot bonds are removed.  This side has raw cut
exactly `2` in the template (the two slot bonds), and every slot's far ends lie on one side.  Extending
the side by the fresh atoms of every slot (labelled like the far ends of the slot) keeps the raw cut
at `2` in every expansion, with the fresh atoms of the chosen slot on the far side. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineRho
open WaveTurbulence WaveTurbulence.Vine

/-- The near side of the slot `s` of the template of `X`, found by inspection of `Vines.png`. -/
def sideOf : VineType → ((ℕ × ℕ) × (ℕ × ℕ)) → Finset ℕ
  | .II, ((2, 1), (3, 1)) => {0, 2, 3}
  | .III, ((2, 4), (3, 5)) => {0, 2, 3}
  | .III, ((4, 7), (6, 8)) => {0, 2, 3, 4, 5, 6}
  | .IV, ((2, 4), (3, 6)) => {0, 2, 3}
  | .IV, ((4, 7), (6, 8)) => {0, 2, 3, 4, 5, 6}
  | .V, ((2, 4), (3, 5)) => {0, 1, 2, 3}
  | .VI, ((2, 4), (3, 5)) => {0, 2, 3}
  | .VI, ((8, 10), (9, 11)) => {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14}
  | .VI, ((6, 13), (7, 14)) => {0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
  | .VII, ((2, 7), (3, 8)) => {0, 2, 3}
  | .VII, ((5, 7), (6, 8)) => {4, 5, 6}
  | .VII, ((7, 9), (8, 10)) => {0, 2, 3, 4, 5, 6, 7, 8}
  | .VIII, ((2, 4), (3, 5)) => {0, 2, 3, 6, 7, 8, 9, 10}
  | .VIII, ((6, 8), (7, 9)) => {0, 1, 2, 3, 4, 5, 6, 7}
  | _, _ => ∅

/-- The finite certificate: every slot of every template is a 2-cut of the template. -/
theorem template_side (X : VineType) :
    ∀ s ∈ X.template.slots,
      s.1.1 ∈ sideOf X s ∧ s.2.1 ∈ sideOf X s ∧ s.1.2 ∉ sideOf X s ∧ s.2.2 ∉ sideOf X s ∧
      sideOf X s ⊆ Finset.range X.template.n ∧ rawCut (sideOf X s) X.template.bonds = 2 ∧
      ∀ t ∈ X.template.slots, (t.1.2 ∈ sideOf X s ↔ t.2.2 ∈ sideOf X s) := by
  cases X <;> decide

theorem template_two_le (X : VineType) : 2 ≤ X.template.n := by cases X <;> decide

theorem template_n_le (X : VineType) : X.template.n ≤ 15 := by cases X <;> decide

theorem template_slots_le (X : VineType) : X.template.slots.length ≤ 3 := by cases X <;> decide

theorem rawCut_congr {W W' : Finset ℕ} (es : List (ℕ × ℕ))
    (h : ∀ p ∈ es, (p.1 ∈ W ↔ p.1 ∈ W') ∧ (p.2 ∈ W ↔ p.2 ∈ W')) : rawCut W es = rawCut W' es := by
  unfold rawCut
  congr 1
  apply List.map_congr_left
  intro p hp
  obtain ⟨h1, h2⟩ := h p hp
  simp only [cutWeight_pair, h1, h2]

theorem rawCut_rail_eq (W : Finset ℕ) (b : ℕ) (ws : List ℕ) (hw : ∀ w ∈ ws, (w ∈ W ↔ b ∈ W))
    (a : ℕ) : rawCut W (railBonds a ws b) = cutWeight W s(a, b) := by
  induction ws generalizing a with
  | nil => simp [railBonds, rawCut]
  | cons w ws ih =>
    have hrail : railBonds a (w :: ws) b = (a, w) :: railBonds w ws b := by
      simp [railBonds]
    rw [hrail, rawCut_cons, ih (fun z hz => hw z (List.mem_cons_of_mem _ hz)) w]
    have hwb := hw w List.mem_cons_self
    simp only [cutWeight_pair, hwb]
    by_cases ha : a ∈ W <;> by_cases hb : b ∈ W <;> simp [ha, hb]

theorem rawCut_rungs_eq_zero (W : Finset ℕ) (us vs : List ℕ)
    (h : ∀ p ∈ List.zip us vs, (p.1 ∈ W ↔ p.2 ∈ W)) :
    rawCut W ((List.zip us vs).flatMap fun p => [p, p]) = 0 := by
  unfold rawCut
  rw [List.sum_eq_zero_iff]
  intro n hn
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
  obtain ⟨q, hq, hpq⟩ := List.mem_flatMap.mp hp
  have hq' : p = q := by simpa using hpq
  subst hq'
  have := h p hq
  simp only [cutWeight_pair, this]
  by_cases hb : p.2 ∈ W <;> simp [hb]

/-- One insertion, with the fresh atoms placed on the side of the far end. -/
theorem insertRungs_cut_ext (W : Finset ℕ) (T : VineTemplate) (s : (ℕ × ℕ) × (ℕ × ℕ)) (k : ℕ)
    (h1 : s.1 ∈ T.bonds) (h2 : s.2 ∈ T.bonds.erase s.1)
    (hT : ∀ p ∈ T.bonds, p.1 < T.n ∧ p.2 < T.n)
    (hs : s.1.1 < T.n ∧ s.1.2 < T.n ∧ s.2.1 < T.n ∧ s.2.2 < T.n) (hy : s.1.2 ∈ W ↔ s.2.2 ∈ W)
    (hW : W ⊆ Finset.range T.n) :
    rawCut (if s.1.2 ∈ W then W ∪ Finset.Ico T.n (T.n + 2 * k) else W)
        (insertRungs T s k).bonds = rawCut W T.bonds := by
  set W' := (if s.1.2 ∈ W then W ∪ Finset.Ico T.n (T.n + 2 * k) else W) with hW'
  have hold : ∀ ℓ, ℓ < T.n → (ℓ ∈ W' ↔ ℓ ∈ W) := by
    intro ℓ hℓ
    rw [hW']
    split_ifs
    · simp only [Finset.mem_union, Finset.mem_Ico]
      constructor
      · rintro (h | h)
        · exact h
        · omega
      · exact Or.inl
    · exact Iff.rfl
  have hnew : ∀ ℓ, T.n ≤ ℓ → ℓ < T.n + 2 * k → (ℓ ∈ W' ↔ s.1.2 ∈ W) := by
    intro ℓ h1 h2
    rw [hW']
    split_ifs with hc
    · simp only [Finset.mem_union, Finset.mem_Ico]
      exact ⟨fun _ => hc, fun _ => Or.inr ⟨h1, h2⟩⟩
    · have : ℓ ∉ W := fun h => by have := Finset.mem_range.mp (hW h); omega
      simp [hc, this]
  by_cases hk : k = 0
  · subst hk
    rw [insertRungs_zero]
    apply rawCut_congr
    intro p hp
    have := hT p hp
    exact ⟨hold _ this.1, hold _ this.2⟩
  · have he1 := rawCut_erase_add W T.bonds s.1 h1
    have he2 := rawCut_erase_add W (T.bonds.erase s.1) s.2 h2
    have hbase : rawCut W' ((T.bonds.erase s.1).erase s.2) = rawCut W ((T.bonds.erase s.1).erase s.2) := by
      apply rawCut_congr
      intro p hp
      have hp' : p ∈ T.bonds := List.mem_of_mem_erase (List.mem_of_mem_erase hp)
      have := hT p hp'
      exact ⟨hold _ this.1, hold _ this.2⟩
    have hrail1 : rawCut W' (railBonds s.1.1 ((List.range k).map (T.n + ·)) s.1.2) =
        cutWeight W s(s.1.1, s.1.2) := by
      rw [rawCut_rail_eq W' s.1.2 _ ?_ s.1.1]
      · simp only [cutWeight_pair, hold _ hs.1, hold _ hs.2.1]
      · intro w hw
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        have := List.mem_range.mp hi
        rw [hnew _ (by omega) (by omega), hold _ hs.2.1]
    have hrail2 : rawCut W' (railBonds s.2.1 ((List.range k).map (T.n + k + ·)) s.2.2) =
        cutWeight W s(s.2.1, s.2.2) := by
      rw [rawCut_rail_eq W' s.2.2 _ ?_ s.2.1]
      · simp only [cutWeight_pair, hold _ hs.2.2.1, hold _ hs.2.2.2]
      · intro w hw
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        have := List.mem_range.mp hi
        rw [hnew _ (by omega) (by omega), hold _ hs.2.2.2, hy]
    have hrungs : rawCut W' ((List.zip ((List.range k).map (T.n + ·))
        ((List.range k).map (T.n + k + ·))).flatMap fun p => [p, p]) = 0 := by
      apply rawCut_rungs_eq_zero
      intro p hp
      obtain ⟨hp1, hp2⟩ := List.of_mem_zip hp
      obtain ⟨i, hi, hpi⟩ := List.mem_map.mp hp1
      obtain ⟨j, hj, hpj⟩ := List.mem_map.mp hp2
      have := List.mem_range.mp hi
      have := List.mem_range.mp hj
      rw [← hpi, ← hpj, hnew _ (by omega) (by omega), hnew _ (by omega) (by omega)]
    simp only [insertRungs, hk, ite_false, rawCut_append, hbase, hrail1, hrail2, hrungs]
    omega

/-- A whole fold of insertions.  The extended side `W'` agrees with `W` below `T.n`, lies in the allocated range,
has the same raw cut, and puts the fresh atoms of a slot on the side of its far end. -/
theorem fold_cut_ext (xs : List (((ℕ × ℕ) × (ℕ × ℕ)) × ℕ)) :
    ∀ (T : VineTemplate) (W : Finset ℕ), (slotMembers xs).Nodup →
      (∀ e ∈ slotMembers xs, e ∈ T.bonds) → (∀ p ∈ T.bonds, p.1 < T.n ∧ p.2 < T.n) →
      (∀ sk ∈ xs, sk.1.1.1 < T.n ∧ sk.1.1.2 < T.n ∧ sk.1.2.1 < T.n ∧ sk.1.2.2 < T.n) →
      (∀ sk ∈ xs, (sk.1.1.2 ∈ W ↔ sk.1.2.2 ∈ W)) → W ⊆ Finset.range T.n →
      ∃ W' : Finset ℕ, W' ⊆ Finset.range (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).n ∧
        (∀ ℓ, ℓ < T.n → (ℓ ∈ W' ↔ ℓ ∈ W)) ∧
        rawCut W' (xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).bonds = rawCut W T.bonds ∧
        ∀ pre post s k, xs = pre ++ (s, k) :: post → ∀ ℓ,
          (pre.foldl (fun U sk => insertRungs U sk.1 sk.2) T).n ≤ ℓ →
          ℓ < (pre.foldl (fun U sk => insertRungs U sk.1 sk.2) T).n + 2 * k → (ℓ ∈ W' ↔ s.1.2 ∈ W) := by
  induction xs with
  | nil =>
    intro T W _ _ _ _ _ hW
    refine ⟨W, by simpa using hW, fun _ _ => Iff.rfl, rfl, ?_⟩
    intro pre post s k h
    exact absurd h (by simp)
  | cons sk xs ih =>
    intro T W hn hm hT hs hy hW
    have hn' : (sk.1.1 :: sk.1.2 :: slotMembers xs).Nodup := hn
    obtain ⟨h1, hn'⟩ := List.nodup_cons.mp hn'
    obtain ⟨h2, htail⟩ := List.nodup_cons.mp hn'
    have hne : sk.1.2 ≠ sk.1.1 := by
      intro he
      exact h1 (List.mem_cons.mpr (Or.inl he.symm))
    have hmem1 := hm sk.1.1 (by simp [slotMembers])
    have hmem2 := hm sk.1.2 (by simp [slotMembers])
    have hsurvive : ∀ e ∈ slotMembers xs, e ∈ (insertRungs T sk.1 sk.2).bonds := by
      intro e he
      apply mem_insertRungs_bonds (hm e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he)))
      · intro heq
        exact h1 (List.mem_cons_of_mem _ (heq ▸ he))
      · intro heq
        exact h2 (heq ▸ he)
    have hsk := hs sk List.mem_cons_self
    have hstep := insertRungs_cut_ext W T sk.1 sk.2 hmem1 ((List.mem_erase_of_ne hne).mpr hmem2) hT
      ⟨hsk.1, hsk.2.1, hsk.2.2.1, hsk.2.2.2⟩ (hy sk List.mem_cons_self) hW
    set W1 := (if sk.1.1.2 ∈ W then W ∪ Finset.Ico T.n (T.n + 2 * sk.2) else W) with hW1
    have hold : ∀ ℓ, ℓ < T.n → (ℓ ∈ W1 ↔ ℓ ∈ W) := by
      intro ℓ hℓ
      rw [hW1]
      split_ifs
      · simp only [Finset.mem_union, Finset.mem_Ico]
        constructor
        · rintro (h | h)
          · exact h
          · omega
        · exact Or.inl
      · exact Iff.rfl
    have hnew : ∀ ℓ, T.n ≤ ℓ → ℓ < T.n + 2 * sk.2 → (ℓ ∈ W1 ↔ sk.1.1.2 ∈ W) := by
      intro ℓ h1 h2
      rw [hW1]
      split_ifs with hc
      · simp only [Finset.mem_union, Finset.mem_Ico]
        exact ⟨fun _ => hc, fun _ => Or.inr ⟨h1, h2⟩⟩
      · have : ℓ ∉ W := fun h => by have := Finset.mem_range.mp (hW h); omega
        simp [hc, this]
    have hatoms : (insertRungs T sk.1 sk.2).n = T.n + 2 * sk.2 := insertRungs_atoms T sk.1 sk.2
    have hW1sub : W1 ⊆ Finset.range (insertRungs T sk.1 sk.2).n := by
      intro ℓ hℓ
      rw [hatoms, Finset.mem_range]
      rw [hW1] at hℓ
      split_ifs at hℓ
      · simp only [Finset.mem_union, Finset.mem_Ico] at hℓ
        rcases hℓ with h | h
        · have := Finset.mem_range.mp (hW h); omega
        · omega
      · have := Finset.mem_range.mp (hW hℓ); omega
    obtain ⟨W', hW'sub, hW'old, hW'cut, hW'new⟩ := ih (insertRungs T sk.1 sk.2) W1 htail hsurvive
      (insertRungs_endpoints T sk.1 sk.2 hT ⟨hsk.1, hsk.2.1, hsk.2.2.1, hsk.2.2.2⟩)
      (by
        intro z hz
        have hh := hs z (List.mem_cons_of_mem _ hz)
        rw [hatoms]
        refine ⟨by omega, by omega, by omega, by omega⟩)
      (by
        intro z hz
        have hh := hs z (List.mem_cons_of_mem _ hz)
        rw [hold _ hh.2.1, hold _ hh.2.2.2]
        exact hy z (List.mem_cons_of_mem _ hz))
      hW1sub
    refine ⟨W', by simpa only [List.foldl_cons] using hW'sub, ?_, ?_, ?_⟩
    · intro ℓ hℓ
      rw [hW'old _ (by rw [hatoms]; omega), hold _ hℓ]
    · simpa only [List.foldl_cons] using hW'cut.trans hstep
    · intro pre post s k hxs ℓ hℓ1 hℓ2
      rcases pre with _ | ⟨p0, pre⟩
      · simp only [List.nil_append, List.cons.injEq] at hxs
        obtain ⟨rfl, _⟩ := hxs
        simp only [List.foldl_nil] at hℓ1 hℓ2
        rw [hW'old _ (by rw [hatoms]; omega), hnew _ hℓ1 hℓ2]
      · simp only [List.cons_append, List.cons.injEq] at hxs
        obtain ⟨rfl, hxs⟩ := hxs
        have hh := hW'new pre post s k hxs ℓ (by simpa only [List.foldl_cons] using hℓ1)
          (by simpa only [List.foldl_cons] using hℓ2)
        rw [hh]
        have hsmem : (s, k) ∈ xs := by rw [hxs]; simp
        have hss := hs (s, k) (List.mem_cons_of_mem _ hsmem)
        rw [hold _ hss.2.1]

end WaveTurbulence.VineRho
