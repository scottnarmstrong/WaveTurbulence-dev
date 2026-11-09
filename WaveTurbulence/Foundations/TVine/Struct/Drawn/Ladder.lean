/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Drawn.LadderMS
public import WaveTurbulence.Foundations.TVine.Core.Lemma19Ins2

/-!
# Inserting ladders at the slots of a T-vine template keeps it a T-vine (packet L3D)

N2 Lemma 5.2, induction step (`research-gamma-half-2/NOTES.md` L834–L835): "Every slot of III–VIII is a 2-edge-cut
whose two sides both contain an interior atom. Inserting k rungs at a slot is k successive rung insertions at 2-cuts of
this kind, so Lemma 1.9(2) applies." Lemma 1.9(2) is L1's `rungInsertion_holds` (path-wise, M4 §5.3, undirected as REF2
requires).

Setting: a base multigraph on `range n₀` with bonds `A + Σ slot bonds`, slots `t : SlotD` with an `x`-side `t.side`
(the side of the slot's 2-edge-cut containing `x, x'`), and `K_t` rungs to insert at each slot, named from a base `b`
on. Slots are processed in order; at the slot being filled, the rungs are inserted one at a time at the `x`-end, so
the cut side `X = t.side ∪ (names of the later slots lying inside t.side)` never changes.

* `Good n₀ A ts`: the decidable side conditions (checked per template by `decide`);
* `tvine_ladders`: the base is a T-vine ⇒ the fully expanded multigraph is a T-vine.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct.Drawn

open TVine WaveTurbulence.TVine.Core

/-! ## Data and side conditions -/

/-- A slot together with the `x`-side of its 2-edge-cut in the base template. -/
structure SlotD where
  sl : Slot
  side : Finset ℕ

/-- The four atoms of a slot lie on one side of `X`. -/
def OneSide (s : Slot) (X : Finset ℕ) : Prop :=
  (s.1.1 ∈ X ∧ s.1.2 ∈ X ∧ s.2.1 ∈ X ∧ s.2.2 ∈ X) ∨ (s.1.1 ∉ X ∧ s.1.2 ∉ X ∧ s.2.1 ∉ X ∧ s.2.2 ∉ X)

instance (s : Slot) (X : Finset ℕ) : Decidable (OneSide s X) := by unfold OneSide; infer_instance

/-- The side conditions of one slot: `x, x' ∈ side ∌ y, y'`, an interior atom on each side, and no bond of `A` crosses
the side. -/
def SlotOK (n₀ : ℕ) (A : Multiset (Sym2 ℕ)) (t : SlotD) : Prop :=
  t.side ⊆ Finset.range n₀ ∧ t.sl.1.1 ∈ t.side ∧ t.sl.2.1 ∈ t.side ∧ t.sl.1.2 ∉ t.side ∧ t.sl.2.2 ∉ t.side ∧
    t.sl.1.2 < n₀ ∧ t.sl.2.2 < n₀ ∧ t.sl.1.1 ≠ t.sl.2.1 ∧
    (∃ i ∈ t.side, i ≠ 0 ∧ i ≠ 1) ∧ (∃ i ∈ Finset.range n₀ \ t.side, i ≠ 0 ∧ i ≠ 1) ∧
    A.countP (fun e => crossB t.side e = true) = 0

instance (n₀ : ℕ) (A : Multiset (Sym2 ℕ)) (t : SlotD) : Decidable (SlotOK n₀ A t) := by
  unfold SlotOK; infer_instance

/-- The side conditions of a template with slots `ts`. -/
def Good (n₀ : ℕ) (A : Multiset (Sym2 ℕ)) (ts : List SlotD) : Prop :=
  WF (Finset.range n₀) A ∧ (∀ t ∈ ts, SlotOK n₀ A t) ∧
    ts.Pairwise (fun t t' => OneSide t'.sl t.side ∧ OneSide t.sl t'.side)

instance (n₀ : ℕ) (A : Multiset (Sym2 ℕ)) (ts : List SlotD) : Decidable (Good n₀ A ts) := by
  unfold Good; infer_instance

/-! ## The expanded multigraph -/

/-- The ladders of all slots, `K` rungs at a slot, names from `b` on (in slot order, `2K` names per slot). -/
def laddersO : List Slot → List ℕ → ℕ → Multiset (ℕ × ℕ)
  | s :: sl, K :: Ks, b => ladderO s (uN b K K) (vN b K K) + laddersO sl Ks (b + 2 * K)
  | _, _, _ => 0

/-- The ladders, undirected. -/
def ladders (sl : List Slot) (Ks : List ℕ) (b : ℕ) : Multiset (Sym2 ℕ) := (laddersO sl Ks b).map mk2

/-- All slot bonds. -/
def slotsMS (sl : List Slot) : Multiset (Sym2 ℕ) := (sl.map slotMS).sum

/-- The rung names of all slots. -/
def namesF (Ks : List ℕ) (b : ℕ) : Finset ℕ := Finset.Ico b (b + 2 * Ks.sum)

/-- The names of the slots of `ts` whose atoms lie inside `X`. -/
def insideNames (X : Finset ℕ) : List SlotD → List ℕ → ℕ → Finset ℕ
  | t :: ts, K :: Ks, b =>
      (if t.sl.1.1 ∈ X then Finset.Ico b (b + 2 * K) else ∅) ∪ insideNames X ts Ks (b + 2 * K)
  | _, _, _ => ∅

theorem ladders_cons (s : Slot) (sl : List Slot) (K : ℕ) (Ks : List ℕ) (b : ℕ) :
    ladders (s :: sl) (K :: Ks) b = ladderMS s (uN b K K) (vN b K K) + ladders sl Ks (b + 2 * K) := by
  simp [ladders, laddersO, ladderMS, Multiset.map_add]

theorem namesF_cons (K : ℕ) (Ks : List ℕ) (b : ℕ) :
    namesF (K :: Ks) b = Finset.Ico b (b + 2 * K) ∪ namesF Ks (b + 2 * K) := by
  unfold namesF
  ext a
  simp only [Finset.mem_union, Finset.mem_Ico, List.sum_cons]
  omega

theorem mem_insideNames {X : Finset ℕ} : ∀ {ts : List SlotD} {Ks : List ℕ} {b a : ℕ},
    a ∈ insideNames X ts Ks b → b ≤ a ∧ a < b + 2 * Ks.sum
  | t :: ts, K :: Ks, b, a, h => by
    simp only [insideNames, Finset.mem_union] at h
    rcases h with h | h
    · split_ifs at h with hx
      · simp only [Finset.mem_Ico] at h; simp only [List.sum_cons]; omega
      · simp at h
    · have := mem_insideNames h; simp only [List.sum_cons]; omega
  | [], _, _, _, h => by simp [insideNames] at h
  | _ :: _, [], _, _, h => by simp [insideNames] at h

theorem insideNames_cons_iff {X : Finset ℕ} {t : SlotD} {ts : List SlotD} {K : ℕ} {Ks : List ℕ} {b a : ℕ}
    (ha : a < b + 2 * K) :
    a ∈ insideNames X (t :: ts) (K :: Ks) b ↔ t.sl.1.1 ∈ X ∧ b ≤ a := by
  simp only [insideNames, Finset.mem_union]
  constructor
  · rintro (h | h)
    · split_ifs at h with hx
      · simp only [Finset.mem_Ico] at h; exact ⟨hx, h.1⟩
      · simp at h
    · have := mem_insideNames h; omega
  · rintro ⟨hx, hb⟩
    left; rw [ite_eq_left hx]; simp only [Finset.mem_Ico]; omega

theorem insideNames_cons_iff' {X : Finset ℕ} {t : SlotD} {ts : List SlotD} {K : ℕ} {Ks : List ℕ} {b a : ℕ}
    (ha : b + 2 * K ≤ a) :
    a ∈ insideNames X (t :: ts) (K :: Ks) b ↔ a ∈ insideNames X ts Ks (b + 2 * K) := by
  simp only [insideNames, Finset.mem_union]
  constructor
  · rintro (h | h)
    · split_ifs at h with hx
      · simp only [Finset.mem_Ico] at h; omega
      · simp at h
    · exact h
  · intro h; exact Or.inr h

/-- Every atom of a bond of the ladders is a slot atom or a name. -/
theorem mem_ladders {n₀ : ℕ} : ∀ {sl : List Slot} {Ks : List ℕ} {b : ℕ}, Ks.length = sl.length →
    (∀ s ∈ sl, s.1.1 < n₀ ∧ s.1.2 < n₀ ∧ s.2.1 < n₀ ∧ s.2.2 < n₀) →
    ∀ e ∈ ladders sl Ks b, ∀ a ∈ e, a < n₀ ∨ a ∈ namesF Ks b
  | s :: sl, K :: Ks, b, hl, hs, e, he, a, ha => by
    rw [ladders_cons, Multiset.mem_add] at he
    rw [namesF_cons, Finset.mem_union]
    rcases he with he | he
    · have h4 := hs s List.mem_cons_self
      rcases mem_ladderMS he a ha with h | h | h | h | h | h
      · exact Or.inl (h ▸ h4.1)
      · exact Or.inl (h ▸ h4.2.1)
      · exact Or.inl (h ▸ h4.2.2.1)
      · exact Or.inl (h ▸ h4.2.2.2)
      · rw [mem_uN le_rfl] at h; right; left; simp only [Finset.mem_Ico]; omega
      · rw [mem_vN le_rfl] at h; right; left; simp only [Finset.mem_Ico]; omega
    · rcases mem_ladders (by simpa using hl) (fun s' hs' => hs s' (List.mem_cons_of_mem _ hs')) e he a ha
        with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  | [], _, _, _, _, e, he, _, _ => by simp [ladders, laddersO] at he
  | _ :: _, [], _, hl, _, _, _, _, _ => by simp at hl

/-- The ladders of slots lying on one side of `X`, with their names on the same side, do not cross `X`. -/
theorem countP_ladders_zero (X side : Finset ℕ) (n₀ : ℕ) : ∀ (ts : List SlotD) (Ks : List ℕ) (b : ℕ),
    Ks.length = ts.length → n₀ ≤ b →
    (∀ t ∈ ts, t.sl.1.1 < n₀ ∧ t.sl.1.2 < n₀ ∧ t.sl.2.1 < n₀ ∧ t.sl.2.2 < n₀) →
    (∀ t ∈ ts, OneSide t.sl side) → (∀ a < n₀, a ∈ X ↔ a ∈ side) →
    (∀ a, b ≤ a → (a ∈ X ↔ a ∈ insideNames side ts Ks b)) →
    (ladders (ts.map SlotD.sl) Ks b).countP (fun e => crossB X e = true) = 0
  | t :: ts, K :: Ks, b, hl, hb, hlt, hone, hlow, hhigh => by
    rw [List.map_cons, ladders_cons, Multiset.countP_add]
    have h4 := hlt t List.mem_cons_self
    have ht := hone t List.mem_cons_self
    rw [countP_ladderMS_zero X t.sl _ _ (t.sl.1.1 ∈ side), countP_ladders_zero X side n₀ ts Ks (b + 2 * K)
      (by simpa using hl) (by omega) (fun t' h' => hlt t' (List.mem_cons_of_mem _ h'))
      (fun t' h' => hone t' (List.mem_cons_of_mem _ h')) hlow]
    · intro a ha
      rw [hhigh a (by omega), insideNames_cons_iff' ha]
    · intro a ha
      rcases ha with h | h | h | h | h | h
      · rw [h, hlow _ h4.1]
      · rw [h, hlow _ h4.2.1]
        rcases ht with ⟨h1, h2, -, -⟩ | ⟨h1, h2, -, -⟩ <;> simp [h1, h2]
      · rw [h, hlow _ h4.2.2.1]
        rcases ht with ⟨h1, -, h2, -⟩ | ⟨h1, -, h2, -⟩ <;> simp [h1, h2]
      · rw [h, hlow _ h4.2.2.2]
        rcases ht with ⟨h1, -, -, h2⟩ | ⟨h1, -, -, h2⟩ <;> simp [h1, h2]
      · rw [mem_uN le_rfl] at h
        rw [hhigh a (by omega), insideNames_cons_iff (by omega)]
        simp only [and_iff_left_iff_imp]; intro; omega
      · rw [mem_vN le_rfl] at h
        rw [hhigh a (by omega), insideNames_cons_iff (by omega)]
        simp only [and_iff_left_iff_imp]; intro; omega
  | [], _, _, _, _, _, _, _, _ => by simp [ladders, laddersO]
  | _ :: _, [], _, hl, _, _, _, _, _ => by simp at hl

/-! ## One rung at the `x`-end of the current slot -/

section step

variable (n₀ : ℕ) (A : Multiset (Sym2 ℕ)) (t : SlotD) (ts : List SlotD) (K : ℕ) (Ks : List ℕ) (b : ℕ)

/-- The vertex set at stage `k` of the slot `t` (the later slots `ts` complete). -/
def stageV (k : ℕ) : Finset ℕ :=
  Finset.range n₀ ∪ (Finset.Ico (b + K - k) (b + K) ∪ Finset.Ico (b + 2 * K - k) (b + 2 * K)) ∪
    namesF Ks (b + 2 * K)

/-- The bond multiset at stage `k` of the slot `t`. -/
def stageMS (k : ℕ) : Multiset (Sym2 ℕ) :=
  A + ladderMS t.sl (uN b K k) (vN b K k) + ladders (ts.map SlotD.sl) Ks (b + 2 * K)

/-- The multigraph at stage `k` of the slot `t`. -/
def stageG (k : ℕ) : UMultigraph ℕ := ofMS (stageV n₀ K Ks b k) (stageMS A t ts K Ks b k)

end step

theorem good_tail {n₀ : ℕ} {A : Multiset (Sym2 ℕ)} {t : SlotD} {ts : List SlotD} (h : Good n₀ A (t :: ts)) :
    Good n₀ (A + slotMS t.sl) ts := by
  obtain ⟨hA, hok, hpw⟩ := h
  have ht := hok t List.mem_cons_self
  obtain ⟨hside, hx, hx', hy, hy', hyn, hyn', -⟩ := ht
  rw [List.pairwise_cons] at hpw
  refine ⟨?_, fun t' h' => ?_, hpw.2⟩
  · apply WF.add hA
    intro e he
    simp only [slotMS, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, mk2] at he
    have h1 := hside hx
    have h2 := hside hx'
    rcases he with rfl | rfl <;> simp_all
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hok t' (List.mem_cons_of_mem _ h')
    refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, ?_⟩
    rw [Multiset.countP_add, a11, zero_add]
    have hos := (hpw.1 t' h').2
    simp only [slotMS, Multiset.insert_eq_cons, ← Multiset.cons_zero, Multiset.countP_cons, Multiset.countP_zero,
      mk2, crossB_mk]
    rcases hos with ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩ <;> simp [b1, b2, b3, b4]

/-- The atoms of the slots of a good template are atoms of the base. -/
theorem good_atoms {n₀ : ℕ} {A : Multiset (Sym2 ℕ)} {ts : List SlotD} (h : Good n₀ A ts) :
    ∀ t ∈ ts, t.sl.1.1 < n₀ ∧ t.sl.1.2 < n₀ ∧ t.sl.2.1 < n₀ ∧ t.sl.2.2 < n₀ := by
  intro t ht
  obtain ⟨hside, hx, hx', -, -, hy, hy', -⟩ := h.2.1 t ht
  exact ⟨Finset.mem_range.mp (hside hx), hy, Finset.mem_range.mp (hside hx'), hy'⟩

theorem stage_wf {n₀ : ℕ} {A : Multiset (Sym2 ℕ)} {t : SlotD} {ts : List SlotD} {K : ℕ} {Ks : List ℕ} {b k : ℕ}
    (hk : k ≤ K) (hl : Ks.length = ts.length) (hg : Good n₀ A (t :: ts)) :
    WF (stageV n₀ K Ks b k) (stageMS A t ts K Ks b k) := by
  have hat := good_atoms hg
  intro e he
  rw [Finset.mem_sym2_iff]
  intro a ha
  unfold stageMS at he
  unfold stageV
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
  rcases Multiset.mem_add.mp he with he | he
  · rcases Multiset.mem_add.mp he with he | he
    · exact Or.inl (Or.inl (Finset.mem_range.mp (Finset.mem_sym2_iff.mp (hg.1 e he) a ha)))
    · have h4 := hat t List.mem_cons_self
      rcases mem_ladderMS he a ha with h | h | h | h | h | h
      · exact Or.inl (Or.inl (h ▸ h4.1))
      · exact Or.inl (Or.inl (h ▸ h4.2.1))
      · exact Or.inl (Or.inl (h ▸ h4.2.2.1))
      · exact Or.inl (Or.inl (h ▸ h4.2.2.2))
      · rw [mem_uN hk] at h; exact Or.inl (Or.inr (Or.inl h))
      · rw [mem_vN hk] at h; exact Or.inl (Or.inr (Or.inr h))
  · rcases mem_ladders (n₀ := n₀) (by simpa using hl)
      (fun s hs => by
        obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hs
        exact hat t' (List.mem_cons_of_mem _ ht')) e he a ha with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (by simpa [namesF] using h)

/-- **One rung insertion.** Stage `k + 1` of the slot `t` is a T-vine if stage `k` is. -/
theorem stage_succ {n₀ : ℕ} {A : Multiset (Sym2 ℕ)} {t : SlotD} {ts : List SlotD} {K : ℕ} {Ks : List ℕ} {b k : ℕ}
    (hk : k < K) (hb : n₀ ≤ b) (hl : Ks.length = ts.length) (hg : Good n₀ A (t :: ts))
    (hT : IsTVineU (stageG n₀ A t ts K Ks b k) 0 1) : IsTVineU (stageG n₀ A t ts K Ks b (k + 1)) 0 1 := by
  obtain ⟨hside, hx, hx', hy, hy', hyn, hyn', hxx', ⟨i₁, hi₁, hi₁0, hi₁1⟩, ⟨i₂, hi₂, hi₂0, hi₂1⟩, hA⟩ :=
    hg.2.1 t List.mem_cons_self
  have hat := good_atoms hg
  have hxn : t.sl.1.1 < n₀ := Finset.mem_range.mp (hside hx)
  have hxn' : t.sl.2.1 < n₀ := Finset.mem_range.mp (hside hx')
  set x := t.sl.1.1 with hxdef
  set y := t.sl.1.2 with hydef
  set x' := t.sl.2.1 with hx'def
  set y' := t.sl.2.2 with hy'def
  set u := b + K - (k + 1) with hu
  set v := b + 2 * K - (k + 1) with hv
  set c := (uN b K k).headD y with hc
  set c' := (vN b K k).headD y' with hc'
  set X := t.side ∪ insideNames t.side ts Ks (b + 2 * K) with hXdef
  set G := stageG n₀ A t ts K Ks b k with hG
  have hwf := stage_wf (K := K) (Ks := Ks) (b := b) (k := k) (by omega) hl hg
  have hcv : c = if k = 0 then y else b + K - k := uN_headD (b := b) (K := K) (k := k) (by omega) y
  have hcv' : c' = if k = 0 then y' else b + 2 * K - k := vN_headD (b := b) (K := K) (k := k) (by omega) y'
  have hGv : G.verts = stageV n₀ K Ks b k := rfl
  -- membership in `X`
  have hXlow : ∀ a < n₀, a ∈ X ↔ a ∈ t.side := by
    intro a ha
    rw [hXdef, Finset.mem_union]
    constructor
    · rintro (h | h)
      · exact h
      · have := mem_insideNames h; omega
    · exact Or.inl
  have hXmid : ∀ a, n₀ ≤ a → a < b + 2 * K → a ∉ X := by
    intro a h1 h2 h
    rw [hXdef, Finset.mem_union] at h
    rcases h with h | h
    · have := Finset.mem_range.mp (hside h); omega
    · have := mem_insideNames h; omega
  have hXhigh : ∀ a, b + 2 * K ≤ a → (a ∈ X ↔ a ∈ insideNames t.side ts Ks (b + 2 * K)) := by
    intro a ha
    rw [hXdef, Finset.mem_union]
    constructor
    · rintro (h | h)
      · have := Finset.mem_range.mp (hside h); omega
      · exact h
    · exact Or.inr
  have hXV : X ⊆ G.verts := by
    intro a ha
    rw [hGv]; unfold stageV
    rw [hXdef, Finset.mem_union] at ha
    rcases ha with h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hside h))
    · have := mem_insideNames h
      exact Finset.mem_union_right _ (by simp only [namesF, Finset.mem_Ico]; omega)
  -- the split of the bond multiset at the `x`-end
  set R := A + ladderRest t.sl (uN b K k) (vN b K k) + ladders (ts.map SlotD.sl) Ks (b + 2 * K) with hR
  have hMk : stageMS A t ts K Ks b k = {s(x, c), s(x', c')} + R := by
    unfold stageMS; rw [ladderMS_split, hR]; abel
  have hMk1 : stageMS A t ts K Ks b (k + 1) = {s(x, u), s(u, c), s(x', v), s(v, c'), s(u, v), s(u, v)} + R := by
    unfold stageMS; rw [uN_succ hk, vN_succ hk, ladderMS_cons_split, hR]; abel
  -- the cut
  have hcut : cut G X = 2 := by
    rw [hG, stageG, cut_ofMS hwf hXV, stageMS, Multiset.countP_add, Multiset.countP_add]
    have h1 : A.countP (fun e => crossB X e = true) = 0 := by
      rw [← hA]
      apply Multiset.countP_congr rfl
      intro e he
      have hes := hg.1 e he
      induction e using Sym2.ind with
      | _ p q =>
        have hp := Finset.mem_range.mp (Finset.mem_sym2_iff.mp hes p (Sym2.mem_mk_left p q))
        have hq := Finset.mem_range.mp (Finset.mem_sym2_iff.mp hes q (Sym2.mem_mk_right p q))
        simp only [crossB_mk, hXlow p hp, hXlow q hq]
    have h2 : (ladderMS t.sl (uN b K k) (vN b K k)).countP (fun e => crossB X e = true) = 2 := by
      apply countP_ladderMS_two
      · exact Finset.mem_union_left _ hx
      · exact Finset.mem_union_left _ hx'
      · rw [hXlow _ hyn]; exact hy
      · rw [hXlow _ hyn']; exact hy'
      · intro a ha; rw [mem_uN (b := b) (K := K) (k := k) (by omega)] at ha; exact hXmid a (by omega) (by omega)
      · intro a ha; rw [mem_vN (b := b) (K := K) (k := k) (by omega)] at ha; exact hXmid a (by omega) (by omega)
    have h3 := countP_ladders_zero X t.side n₀ ts Ks (b + 2 * K) hl (by omega)
      (fun t' h' => hat t' (List.mem_cons_of_mem _ h'))
      (fun t' h' => ((List.pairwise_cons.mp hg.2.2).1 t' h').1) hXlow hXhigh
    rw [h1, h2, h3]
  -- the four ends and their sides
  have hxX : x ∈ X := Finset.mem_union_left _ hx
  have hxX' : x' ∈ X := Finset.mem_union_left _ hx'
  have hcV : c ∈ G.verts \ X := by
    rw [hcv]
    split_ifs with h0
    · refine Finset.mem_sdiff.mpr ⟨?_, by rw [hXlow _ hyn]; exact hy⟩
      rw [hGv]; unfold stageV; simp only [Finset.mem_union, Finset.mem_range]; exact Or.inl (Or.inl hyn)
    · refine Finset.mem_sdiff.mpr ⟨?_, hXmid _ (by omega) (by omega)⟩
      rw [hGv]; unfold stageV namesF; simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_range]; omega
  have hcV' : c' ∈ G.verts \ X := by
    rw [hcv']
    split_ifs with h0
    · refine Finset.mem_sdiff.mpr ⟨?_, by rw [hXlow _ hyn']; exact hy'⟩
      rw [hGv]; unfold stageV; simp only [Finset.mem_union, Finset.mem_range]; exact Or.inl (Or.inl hyn')
    · refine Finset.mem_sdiff.mpr ⟨?_, hXmid _ (by omega) (by omega)⟩
      rw [hGv]; unfold stageV namesF; simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_range]; omega
  -- multiplicities of the two cut bonds
  have hmult : ∀ e, G.mult e = ({s(x, c), s(x', c')} : Multiset (Sym2 ℕ)).count e + R.count e := by
    intro e; rw [hG, stageG, ofMS_mult_of_wf hwf, hMk, Multiset.count_add]
  have hm1 : G.mult s(x, c) ≠ 0 := by
    rw [hmult]; simp
  have hm2 : G.mult s(x', c') ≠ 0 := by
    rw [hmult]; simp
  have hsame : s(x, c) = s(x', c') → G.mult s(x, c) = 2 := by
    intro h
    exfalso
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hxx' h1
    · exact (Finset.mem_sdiff.mp hcV').2 (h1 ▸ hxX)
  -- fresh names
  have huV : u ∉ G.verts := by
    rw [hGv]; unfold stageV namesF; simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_range]; omega
  have hvV : v ∉ G.verts := by
    rw [hGv]; unfold stageV namesF; simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_range]; omega
  have huv : u ≠ v := by omega
  -- interior atoms on both sides
  have hiX : ∃ i ∈ X, i ≠ 0 ∧ i ≠ 1 := ⟨i₁, Finset.mem_union_left _ hi₁, hi₁0, hi₁1⟩
  have hiY : ∃ i ∈ G.verts \ X, i ≠ 0 ∧ i ≠ 1 := by
    obtain ⟨hi₂n, hi₂s⟩ := Finset.mem_sdiff.mp hi₂
    have hi₂n' := Finset.mem_range.mp hi₂n
    refine ⟨i₂, Finset.mem_sdiff.mpr ⟨?_, by rw [hXlow _ hi₂n']; exact hi₂s⟩, hi₂0, hi₂1⟩
    rw [hGv]; unfold stageV; exact Finset.mem_union_left _ (Finset.mem_union_left _ hi₂n)
  -- the insertion
  have hins := (rungInsertion_holds G 0 1 X x c x' c' u v hT hXV hcut hxX hxX' hcV hcV' hm1 hm2 hsame hiX hiY
    huV hvV huv).1
  have hcG : c ∈ G.verts := (Finset.mem_sdiff.mp hcV).1
  have hcG' : c' ∈ G.verts := (Finset.mem_sdiff.mp hcV').1
  have hxG : x ∈ G.verts := hXV hxX
  have hxG' : x' ∈ G.verts := hXV hxX'
  have heq : stageG n₀ A t ts K Ks b (k + 1) = insertRung G x c x' c' u v := by
    apply Core.ext
    · show stageV n₀ K Ks b (k + 1) = insert u (insert v (G.verts ∪ {x, c, x', c'}))
      have hsub : ({x, c, x', c'} : Finset ℕ) ⊆ G.verts := by
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl | rfl
        · exact hxG
        · exact hcG
        · exact hxG'
        · exact hcG'
      rw [Finset.union_eq_left.mpr hsub, hGv]
      ext a
      unfold stageV namesF
      simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_range, Finset.mem_insert]
      omega
    · intro e
      rw [insertRung_mult, hmult, stageG, ofMS_mult_of_wf (stage_wf (K := K) (Ks := Ks) (b := b) (k := k + 1) (by omega) hl hg), hMk1, Multiset.count_add,
        Multiset.count_add]
      omega
  rw [heq]
  exact hins

/-! ## All slots -/

theorem stageV_zero (n₀ K : ℕ) (Ks : List ℕ) (b : ℕ) :
    stageV n₀ K Ks b 0 = Finset.range n₀ ∪ namesF Ks (b + 2 * K) := by
  unfold stageV; simp

theorem stageV_full (n₀ K : ℕ) (Ks : List ℕ) (b : ℕ) :
    stageV n₀ K Ks b K = Finset.range n₀ ∪ namesF (K :: Ks) b := by
  unfold stageV
  rw [namesF_cons]
  ext a
  unfold namesF
  simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_range]
  omega

/-- **Inserting the ladders at every slot of a good template keeps a T-vine a T-vine** (N2 Lemma 5.2, induction
via N2 Lemma 1.9(2)). -/
theorem tvine_ladders (n₀ : ℕ) : ∀ (ts : List SlotD) (A : Multiset (Sym2 ℕ)) (Ks : List ℕ) (b : ℕ),
    Ks.length = ts.length → n₀ ≤ b → Good n₀ A ts →
    IsTVineU (ofMS (Finset.range n₀) (A + slotsMS (ts.map SlotD.sl))) 0 1 →
    IsTVineU (ofMS (Finset.range n₀ ∪ namesF Ks b) (A + ladders (ts.map SlotD.sl) Ks b)) 0 1
  | [], A, Ks, b, hl, _, _, hT => by
    have hK : Ks = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hK
    simpa [namesF, ladders, laddersO, slotsMS] using hT
  | t :: ts, A, Ks, b, hl, hb, hg, hT => by
    obtain ⟨K, Ks', rfl⟩ : ∃ K Ks', Ks = K :: Ks' := by
      cases Ks with
      | nil => simp at hl
      | cons K Ks' => exact ⟨K, Ks', rfl⟩
    have hl' : Ks'.length = ts.length := by simpa using hl
    have hstage : ∀ k, k ≤ K → IsTVineU (stageG n₀ A t ts K Ks' b k) 0 1 := by
      intro k
      induction k with
      | zero =>
        intro _
        have h := tvine_ladders n₀ ts (A + slotMS t.sl) Ks' (b + 2 * K) hl' (by omega) (good_tail hg)
          (by
            have : A + slotMS t.sl + slotsMS (ts.map SlotD.sl) = A + slotsMS ((t :: ts).map SlotD.sl) := by
              simp [slotsMS, add_assoc]
            rw [this]; exact hT)
        have he : stageG n₀ A t ts K Ks' b 0 =
            ofMS (Finset.range n₀ ∪ namesF Ks' (b + 2 * K)) (A + slotMS t.sl + ladders (ts.map SlotD.sl) Ks' (b + 2 * K)) := by
          unfold stageG stageMS
          rw [stageV_zero, uN_zero, vN_zero, ladderMS_nil]
        rw [he]; exact h
      | succ k ih =>
        intro hk
        exact stage_succ (by omega) hb hl' hg (ih (by omega))
    have he : stageG n₀ A t ts K Ks' b K =
        ofMS (Finset.range n₀ ∪ namesF (K :: Ks') b) (A + ladders ((t :: ts).map SlotD.sl) (K :: Ks') b) := by
      unfold stageG stageMS
      rw [stageV_full, List.map_cons, ladders_cons, add_assoc]
    rw [← he]
    exact hstage K le_rfl

end WaveTurbulence.TVine.Struct.Drawn
