/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.Band
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.Pieces
public import WaveTurbulence.Foundations.TVine.Struct.Statement
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitDecode2
public import WaveTurbulence.Foundations.Molecule.MoleculeGroups
import Mathlib.Tactic
/-! # Every T-vine has a band labelling (packet L5a, item H)

From N3 Theorem 6 (L3's published `TVine.Struct.LayervineStatement`) and N2 Prop 1.17(b) (`PieceShapeStatement`):
label the upper joint `0`, the lower joint `1`, then the atoms of the spine pieces `G₁, …, G_r` (from the lower joint)
and of the pendant pieces `Y₁, …, Y_s`, piece by piece. Pieces have at most three atoms, bonds between different pieces
join consecutive spine members or consecutive pendant members, or leave the pendant; so every bond is short (labels at
distance `≤ bandW = 6`) except the bonds from `G_r` to the upper joint (at most two) and the two exits of the pendant.
Every directed arc has multiplicity at most four (atoms have degree four). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open Finset

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D]

/-! ## Positions in a list of pieces -/

/-- The atoms of a list of atom sets, set by set. -/
noncomputable def atomList (L : List (Finset V)) : List V := L.flatMap Finset.toList

/-- The offset of the `i`-th set. -/
noncomputable def offAt (L : List (Finset V)) (i : ℕ) : ℕ := ((L.take i).flatMap Finset.toList).length

theorem atomList_split (L : List (Finset V)) (i : ℕ) (hi : i < L.length) :
    atomList L = (L.take i).flatMap Finset.toList ++ (L[i].toList ++ (L.drop (i + 1)).flatMap Finset.toList) := by
  unfold atomList
  calc L.flatMap Finset.toList = (L.take i ++ L.drop i).flatMap Finset.toList := by rw [List.take_append_drop]
    _ = _ := by rw [List.drop_eq_getElem_cons hi, List.flatMap_append, List.flatMap_cons]

theorem offAt_succ (L : List (Finset V)) (i : ℕ) (hi : i < L.length) : offAt L (i + 1) = offAt L i + L[i].card := by
  unfold offAt
  rw [List.take_succ_eq_append_getElem hi, List.flatMap_append, List.length_append]
  simp

theorem idxOf_bounds (L : List (Finset V)) (hnd : (atomList L).Nodup) (i : ℕ) (hi : i < L.length) {v : V}
    (hv : v ∈ L[i]) : offAt L i ≤ (atomList L).idxOf v ∧ (atomList L).idxOf v < offAt L i + L[i].card := by
  have hsplit := atomList_split L i hi
  have hvl : v ∈ L[i].toList := Finset.mem_toList.mpr hv
  have hnot : v ∉ (L.take i).flatMap Finset.toList := by
    intro hmem
    rw [hsplit] at hnd
    exact List.disjoint_of_nodup_append hnd hmem (List.mem_append_left _ hvl)
  rw [hsplit, List.idxOf_append_of_notMem hnot, List.idxOf_append_of_mem hvl]
  refine ⟨Nat.le_add_right _ _, ?_⟩
  unfold offAt
  have := List.idxOf_lt_length_of_mem hvl
  rw [Finset.length_toList] at this
  omega

/-- Two consecutive sets: their atoms are at distance less than the sum of their sizes. -/
theorem idxOf_consecutive (L : List (Finset V)) (hnd : (atomList L).Nodup) (i : ℕ) (hi : i + 1 < L.length)
    {u v : V} (hu : u ∈ L[i]) (hv : v ∈ L[i + 1]) :
    (atomList L).idxOf u < (atomList L).idxOf v ∧
      (atomList L).idxOf v < (atomList L).idxOf u + L[i].card + L[i + 1].card := by
  have h1 := idxOf_bounds L hnd i (by omega) hu
  have h2 := idxOf_bounds L hnd (i + 1) hi hv
  rw [offAt_succ L i (by omega)] at h2
  omega

theorem idxOf_same (L : List (Finset V)) (hnd : (atomList L).Nodup) (i : ℕ) (hi : i < L.length)
    {u v : V} (hu : u ∈ L[i]) (hv : v ∈ L[i]) :
    (atomList L).idxOf v < (atomList L).idxOf u + L[i].card ∧ (atomList L).idxOf u < (atomList L).idxOf v + L[i].card := by
  have h1 := idxOf_bounds L hnd i hi hu
  have h2 := idxOf_bounds L hnd i hi hv
  omega

/-- The band labelling: upper joint `0`, lower joint `1`, the listed atoms from `2`. -/
noncomputable def bandLabel (a b : V) (A : List V) (v : V) : ℕ :=
  if v = a then 0 else if v = b then 1 else A.idxOf v + 2

/-! ## Helpers on the Theorem 6 data -/

theorem mem_unionAll {l : List (Finset V)} {w : V} : w ∈ TVine.Struct.unionAll l ↔ ∃ P ∈ l, w ∈ P := by
  induction l with
  | nil => simp [TVine.Struct.unionAll]
  | cons P l ih =>
    simp only [TVine.Struct.unionAll, List.foldr_cons, Finset.mem_union, List.mem_cons] at ih ⊢
    rw [ih]
    constructor
    · rintro (h | ⟨Q, hQ, hw⟩)
      · exact ⟨P, Or.inl rfl, h⟩
      · exact ⟨Q, Or.inr hQ, hw⟩
    · rintro ⟨Q, rfl | hQ, hw⟩
      · exact Or.inl hw
      · exact Or.inr ⟨Q, hQ, hw⟩

theorem extSpine_length (a b : V) (sp : List (Finset V)) :
    (TVine.Struct.extSpine a b sp).length = sp.length + 2 := by
  simp [TVine.Struct.extSpine]

theorem extSpine_get_zero (a b : V) (sp : List (Finset V)) (h : 0 < (TVine.Struct.extSpine a b sp).length) :
    (TVine.Struct.extSpine a b sp).get ⟨0, h⟩ = {b} := by
  simp [TVine.Struct.extSpine]

theorem extSpine_get_succ (a b : V) (sp : List (Finset V)) (i : ℕ) (hi : i < sp.length)
    (h : i + 1 < (TVine.Struct.extSpine a b sp).length) :
    (TVine.Struct.extSpine a b sp).get ⟨i + 1, h⟩ = sp[i] := by
  simp [TVine.Struct.extSpine, List.getElem_append_left hi]

theorem extSpine_get_last (a b : V) (sp : List (Finset V))
    (h : sp.length + 1 < (TVine.Struct.extSpine a b sp).length) :
    (TVine.Struct.extSpine a b sp).get ⟨sp.length + 1, h⟩ = {a} := by
  simp [TVine.Struct.extSpine]

/-- A bond between two atom sets is counted by `crossBonds`. -/
theorem crossBonds_pos (M : Molecule V D) {P Q : Finset V} {x : D} (hx : M.out x = true)
    (hu : M.atom x ∈ P) (hv : M.atom (M.mate x) ∈ Q) : 0 < TVine.Struct.crossBonds M P Q ∧
      0 < TVine.Struct.crossBonds M Q P := by
  unfold TVine.Struct.crossBonds
  constructor <;> refine Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · simp [Molecule.bonds, hx]
  · exact Or.inl ⟨hu, hv⟩
  · simp [Molecule.bonds, hx]
  · exact Or.inr ⟨hu, hv⟩

/-! ## The labelling theorem -/

/-- The data of N3 Theorem 6 that the labelling uses, for the labelling `(v₁, v₂) = (a, b)`. -/
structure SpineData (M : Molecule V D) (S : Finset V) (a b : V) where
  sp : List (Finset V)
  pd : List (Finset V)
  nodup : (sp ++ pd).Nodup
  pieces : (sp ++ pd).toFinset = M.pieces S a b
  /-- non-consecutive members of the extended spine are not joined -/
  noncons : ∀ i j : Fin (TVine.Struct.extSpine a b sp).length, i.val + 2 ≤ j.val →
    TVine.Struct.crossBonds M ((TVine.Struct.extSpine a b sp).get i) ((TVine.Struct.extSpine a b sp).get j) = 0
  /-- consecutive members are joined by one or two bonds -/
  cons : ∀ i j : Fin (TVine.Struct.extSpine a b sp).length, i.val + 1 = j.val →
    TVine.Struct.crossBonds M ((TVine.Struct.extSpine a b sp).get i) ((TVine.Struct.extSpine a b sp).get j) = 1 ∨
    TVine.Struct.crossBonds M ((TVine.Struct.extSpine a b sp).get i) ((TVine.Struct.extSpine a b sp).get j) = 2
  /-- non-consecutive pendant pieces are not joined -/
  pnoncons : ∀ k l : Fin pd.length, k.val + 2 ≤ l.val → TVine.Struct.crossBonds M (pd.get k) (pd.get l) = 0
  /-- the pendant has exactly two exits -/
  pexits : pd ≠ [] → TVine.Struct.crossBonds M (TVine.Struct.unionAll pd) (S \ TVine.Struct.unionAll pd) = 2

/-- Theorem 6 (i)–(iii) gives the spine data. -/
noncomputable def spineData_of {M : Molecule V D} {S : Finset V} {a b : V}
    (h : TVine.Struct.LayervineStructure M S a b) : SpineData M S a b := by
  classical
  let sp := h.choose
  let pd := h.choose_spec.choose
  have H := h.choose_spec.choose_spec
  obtain ⟨hnd, hset, -, -, hcons, hnon, -, -, hpend⟩ := H
  refine ⟨sp, pd, hnd, hset, hnon, hcons, ?_, ?_⟩
  · intro k l hkl
    rcases hpend with ⟨hpd, -⟩ | ⟨Ys, C, hpd, -, -, -, hpn, -⟩
    · exact absurd k.isLt (by simp [pd, hpd])
    · exact hpn k l hkl
  · intro hne
    rcases hpend with ⟨hpd, -⟩ | ⟨Ys, C, hpd, -, -, -, -, hex⟩
    · exact absurd hpd hne
    · obtain ⟨x, x', hT, -⟩ := hex ⟨0, List.length_pos_iff.mpr hne⟩
      have h1 := hT.1
      simp only [List.drop_zero] at h1
      exact h1

theorem crossBonds_comm (M : Molecule V D) (P Q : Finset V) :
    TVine.Struct.crossBonds M P Q = TVine.Struct.crossBonds M Q P := by
  unfold TVine.Struct.crossBonds
  congr 1
  ext x
  simp only [Finset.mem_filter]
  tauto

section Adjacency
variable {M : Molecule V D} {S : Finset V} {a b : V} (Dt : SpineData M S a b)

/-- Two spine pieces joined by a bond are consecutive. -/
theorem spine_adjacent {i j : ℕ} (hi : i < Dt.sp.length) (hj : j < Dt.sp.length)
    (hpos : 0 < TVine.Struct.crossBonds M Dt.sp[i] Dt.sp[j]) : j ≤ i + 1 ∧ i ≤ j + 1 := by
  have hl := extSpine_length a b Dt.sp
  by_contra hc
  rcases Nat.lt_or_ge (i + 1) j with h | h
  · have := Dt.noncons ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ (by simp; omega)
    rw [extSpine_get_succ a b Dt.sp i hi, extSpine_get_succ a b Dt.sp j hj] at this
    omega
  · have := Dt.noncons ⟨j + 1, by omega⟩ ⟨i + 1, by omega⟩ (by simp; omega)
    rw [extSpine_get_succ a b Dt.sp i hi, extSpine_get_succ a b Dt.sp j hj, crossBonds_comm] at this
    omega

/-- A spine piece joined to the lower joint `b` is the first one. -/
theorem spine_adjacent_b {j : ℕ} (hj : j < Dt.sp.length)
    (hpos : 0 < TVine.Struct.crossBonds M {b} Dt.sp[j]) : j = 0 := by
  have hl := extSpine_length a b Dt.sp
  by_contra hc
  have := Dt.noncons ⟨0, by omega⟩ ⟨j + 1, by omega⟩ (by simp; omega)
  rw [extSpine_get_zero, extSpine_get_succ a b Dt.sp j hj] at this
  omega

/-- A spine piece joined to the upper joint `a` is the last one. -/
theorem spine_adjacent_a {j : ℕ} (hj : j < Dt.sp.length)
    (hpos : 0 < TVine.Struct.crossBonds M Dt.sp[j] {a}) : j + 1 = Dt.sp.length := by
  have hl := extSpine_length a b Dt.sp
  by_contra hc
  have := Dt.noncons ⟨j + 1, by omega⟩ ⟨Dt.sp.length + 1, by omega⟩ (by simp; omega)
  rw [extSpine_get_succ a b Dt.sp j hj, extSpine_get_last] at this
  omega

/-- The last spine piece and the upper joint are joined by at most two bonds. -/
theorem spine_last_bonds (hne : Dt.sp ≠ []) :
    TVine.Struct.crossBonds M (Dt.sp.getLast hne) {a} ≤ 2 := by
  have hl := extSpine_length a b Dt.sp
  have hpos : 0 < Dt.sp.length := List.length_pos_iff.mpr hne
  have := Dt.cons ⟨Dt.sp.length, by omega⟩ ⟨Dt.sp.length + 1, by omega⟩ rfl
  have e : (TVine.Struct.extSpine a b Dt.sp).get ⟨Dt.sp.length, by omega⟩ = Dt.sp.getLast hne := by
    obtain ⟨k, hk⟩ : ∃ k, Dt.sp.length = k + 1 := ⟨Dt.sp.length - 1, by omega⟩
    have := extSpine_get_succ a b Dt.sp k (by omega) (by omega)
    simp only [hk] at this ⊢
    rw [this, List.getLast_eq_getElem]
    congr 1; omega
  rw [e, extSpine_get_last] at this
  omega

/-- Two pendant pieces joined by a bond are consecutive. -/
theorem pendant_adjacent {k l : ℕ} (hk : k < Dt.pd.length) (hl : l < Dt.pd.length)
    (hpos : 0 < TVine.Struct.crossBonds M Dt.pd[k] Dt.pd[l]) : l ≤ k + 1 ∧ k ≤ l + 1 := by
  by_contra hc
  rcases Nat.lt_or_ge (k + 1) l with h | h
  · have := Dt.pnoncons ⟨k, hk⟩ ⟨l, hl⟩ (by simp; omega)
    simp only [List.get_eq_getElem] at this
    omega
  · have := Dt.pnoncons ⟨l, hl⟩ ⟨k, hk⟩ (by simp; omega)
    simp only [List.get_eq_getElem] at this
    rw [crossBonds_comm] at this
    omega

end Adjacency

section Labelling
variable {M : Molecule V D} {S : Finset V} {a b : V}

/-- Every directed arc of a group occurs at most four times (atoms have degree at most four). -/
theorem short_mult_le (hM : M.IsMolecule) (hSat : S ⊆ M.atoms) {f : V → ℕ} (hinj : Set.InjOn f S) :
    ∀ q, ShortArc q → (WaveTurbulence.ClassCount.groupArcs M S f).count q ≤ 4 := by
  classical
  intro q _
  unfold WaveTurbulence.ClassCount.groupArcs
  rw [Multiset.count_map, ← Finset.filter_val, Finset.card_val, Finset.filter_filter]
  by_cases h : ∃ x, (M.out x = true ∧ M.InGroup S x) ∧ q = (f (M.atom x), f (M.atom (M.mate x)))
  · obtain ⟨x₀, hx₀, hq⟩ := h
    calc _ ≤ ((M.dartsAt (M.atom x₀)).filter (M.InGroup S)).card := by
          apply Finset.card_le_card
          intro x hx
          obtain ⟨-, ⟨-, hxS⟩, hqx⟩ := Finset.mem_filter.mp hx
          refine Finset.mem_filter.mpr ⟨(Mole.mem_dartsAt M _ x).mpr ?_, hxS⟩
          have := congrArg Prod.fst (hq.symm.trans hqx)
          exact (hinj hx₀.2.1 hxS.1 this).symm
      _ = M.degIn S (M.atom x₀) := rfl
      _ ≤ M.deg (M.atom x₀) := Mole.degIn_le_deg M S _
      _ ≤ 4 := Mole.deg_le_four M hM (hSat hx₀.2.1)
  · push Not at h
    rw [Finset.card_eq_zero.mpr]
    · omega
    · refine Finset.filter_eq_empty_iff.mpr fun x hx h' => h x ?_ h'.2
      exact h'.1

/-- At most four arcs of the band labelling are long. -/
theorem long_count_le (Dt : SpineData M S a b) (hab : a ≠ b) (haS : a ∈ S) (hbS : b ∈ S)
    (hLp : ∀ P ∈ Dt.sp ++ Dt.pd, P ∈ M.pieces S a b)
    (hLsz : ∀ (i : ℕ) (hi : i < (Dt.sp ++ Dt.pd).length), (Dt.sp ++ Dt.pd)[i].card ≤ 3)
    (hAnd : (atomList (Dt.sp ++ Dt.pd)).Nodup)
    (hloc : ∀ v ∈ (S.erase a).erase b, ∃ i, ∃ hi : i < (Dt.sp ++ Dt.pd).length, v ∈ (Dt.sp ++ Dt.pd)[i])
    (haI : a ∉ (S.erase a).erase b) (hbI : b ∉ (S.erase a).erase b)
    {f : V → ℕ} (hfa : f a = 0) (hfb : f b = 1)
    (hfI : ∀ v ∈ (S.erase a).erase b, f v = (atomList (Dt.sp ++ Dt.pd)).idxOf v + 2) :
    Multiset.card ((WaveTurbulence.ClassCount.groupArcs M S f).filter fun q => ¬ ShortArc q) ≤ 4 := by
  classical
  set L := Dt.sp ++ Dt.pd with hL
  set A := atomList L with hA
  set I := (S.erase a).erase b with hI
  set H := TVine.Struct.unionAll Dt.pd with hH
  have hHI : ∀ w ∈ H, w ∈ I := by
    intro w hw
    obtain ⟨Q, hQ, hwQ⟩ := mem_unionAll.mp hw
    exact pieces_subset M (hLp Q (List.mem_append_right _ hQ)) hwQ
  have hspH : ∀ (i : ℕ) (hi : i < Dt.sp.length) (w : V), w ∈ Dt.sp[i] → w ∉ H := by
    intro i hi w hw hwH
    obtain ⟨Q, hQ, hwQ⟩ := mem_unionAll.mp hwH
    have hP := hLp _ (List.mem_append_left _ (List.getElem_mem hi))
    have hQ' := hLp _ (List.mem_append_right _ hQ)
    have heq := piece_eq_of_mem M hP hQ' hw hwQ
    exact List.disjoint_of_nodup_append Dt.nodup (List.getElem_mem hi) (heq ▸ hQ)
  have hpdH : ∀ (k : ℕ) (hk : k < Dt.pd.length) (w : V), w ∈ Dt.pd[k] → w ∈ H :=
    fun k hk w hw => mem_unionAll.mpr ⟨_, List.getElem_mem hk, hw⟩
  have hLsp : ∀ (i : ℕ) (hi : i < Dt.sp.length), L[i]'(by simp [hL]; omega) = Dt.sp[i] :=
    fun i hi => List.getElem_append_left hi
  have hLpd : ∀ (i : ℕ) (hi : i < L.length) (h : Dt.sp.length ≤ i), L[i] = Dt.pd[i - Dt.sp.length]'(by
      simp [hL] at hi; omega) :=
    fun i hi h => List.getElem_append_right h
  -- the two long sets
  let T1 : Finset D := if h : Dt.sp ≠ [] then M.bonds.filter (fun x =>
      (M.atom x ∈ Dt.sp.getLast h ∧ M.atom (M.mate x) ∈ ({a} : Finset V)) ∨
      (M.atom x ∈ ({a} : Finset V) ∧ M.atom (M.mate x) ∈ Dt.sp.getLast h)) else ∅
  let T2 : Finset D := if Dt.pd ≠ [] then M.bonds.filter (fun x =>
      (M.atom x ∈ H ∧ M.atom (M.mate x) ∈ S \ H) ∨ (M.atom x ∈ S \ H ∧ M.atom (M.mate x) ∈ H)) else ∅
  have hT1 : T1.card ≤ 2 := by
    simp only [T1]
    split_ifs with h
    · exact spine_last_bonds Dt h
    · simp
  have hT2 : T2.card ≤ 2 := by
    simp only [T2]
    split_ifs with h
    · exact (Dt.pexits h).le
    · simp
  -- short arcs between pieces at most one apart
  have shortI : ∀ (i j : ℕ) (hi : i < L.length) (hj : j < L.length) {u v : V}, u ∈ L[i] → v ∈ L[j] →
      j ≤ i + 1 → i ≤ j + 1 → ShortArc (A.idxOf u + 2, A.idxOf v + 2) := by
    intro i j hi hj u v hu hv h1 h2
    simp only [ShortArc, bandW_eq]
    have ci := hLsz i hi
    have cj := hLsz j hj
    rcases Nat.lt_trichotomy i j with h | rfl | h
    · obtain rfl : j = i + 1 := by omega
      have := idxOf_consecutive L hAnd i hj hu hv
      rw [← hA] at this
      omega
    · have := idxOf_same L hAnd i hi hu hv
      rw [← hA] at this
      omega
    · obtain rfl : i = j + 1 := by omega
      have := idxOf_consecutive L hAnd j hi hv hu
      rw [← hA] at this
      omega
  have key : ∀ x, M.out x = true → M.InGroup S x →
      ¬ ShortArc (f (M.atom x), f (M.atom (M.mate x))) → x ∈ T1 ∪ T2 := by
    intro x hx hxS hns
    have hxb : x ∈ M.bonds := by simp [Molecule.bonds, hx]
    have hlen : L.length = Dt.sp.length + Dt.pd.length := by simp [hL]
    -- `x` leaves the pendant
    have inT2 : (M.atom x ∈ H ∧ M.atom (M.mate x) ∉ H) ∨ (M.atom x ∉ H ∧ M.atom (M.mate x) ∈ H) → x ∈ T1 ∪ T2 := by
      intro h
      have hne : Dt.pd ≠ [] := by
        intro he
        have : H = ∅ := by rw [hH, he]; rfl
        rcases h with ⟨h, -⟩ | ⟨-, h⟩ <;> simp [this] at h
      refine Finset.mem_union_right _ ?_
      simp only [T2, if_pos hne]
      refine Finset.mem_filter.mpr ⟨hxb, ?_⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, Finset.mem_sdiff.mpr ⟨hxS.2, h2⟩⟩
      · exact Or.inr ⟨Finset.mem_sdiff.mpr ⟨hxS.1, h1⟩, h2⟩
    have aH : a ∉ H := fun h => haI (hHI a h)
    have bH : b ∉ H := fun h => hbI (hHI b h)
    -- location of the two ends
    have hS2 : ∀ w ∈ S, w = a ∨ w = b ∨ w ∈ I := by
      intro w hw
      by_cases h1 : w = a
      · exact Or.inl h1
      · by_cases h2 : w = b
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (by simp [hI, h1, h2, hw]))
    -- interior end: its piece is a spine or a pendant piece
    have side : ∀ w ∈ I, ∃ i, ∃ hi : i < L.length, w ∈ L[i] ∧
        ((i < Dt.sp.length ∧ w ∉ H) ∨ (Dt.sp.length ≤ i ∧ w ∈ H)) := by
      intro w hw
      obtain ⟨i, hi, hwi⟩ := hloc w hw
      refine ⟨i, hi, hwi, ?_⟩
      rcases Nat.lt_or_ge i Dt.sp.length with h | h
      · exact Or.inl ⟨h, hspH i h w (hLsp i h ▸ hwi)⟩
      · exact Or.inr ⟨h, hpdH (i - Dt.sp.length) (by omega) w (hLpd i hi h ▸ hwi)⟩
    rcases hS2 _ hxS.1 with hu | hu | hu <;> rcases hS2 _ hxS.2 with hv | hv | hv
    -- both joints
    · exfalso; apply hns; rw [hu, hv, hfa]; simp only [ShortArc, bandW_eq]; omega
    · exfalso; apply hns; rw [hu, hv, hfa, hfb]; simp only [ShortArc, bandW_eq]; omega
    -- u = a, v interior
    · obtain ⟨j, hj, hvj, (⟨hjs, hvH⟩ | ⟨hjs, hvH⟩)⟩ := side _ hv
      · have hpos := (crossBonds_pos M hx (show M.atom x ∈ ({a} : Finset V) by simp [hu])
          (show M.atom (M.mate x) ∈ Dt.sp[j] from hLsp j hjs ▸ hvj)).2
        have hlast := spine_adjacent_a Dt hjs hpos
        have hne : Dt.sp ≠ [] := List.ne_nil_of_length_pos (by omega)
        refine Finset.mem_union_left _ ?_
        simp only [T1, dif_pos hne]
        refine Finset.mem_filter.mpr ⟨hxb, Or.inr ⟨by simp [hu], ?_⟩⟩
        rw [List.getLast_eq_getElem]
        have : Dt.sp.length - 1 = j := by omega
        simp only [this]
        exact hLsp j hjs ▸ hvj
      · exact inT2 (Or.inr ⟨hu ▸ aH, hvH⟩)
    · exfalso; apply hns; rw [hu, hv, hfa, hfb]; simp only [ShortArc, bandW_eq]; omega
    · exfalso; apply hns; rw [hu, hv, hfb]; simp only [ShortArc, bandW_eq]; omega
    -- u = b, v interior
    · obtain ⟨j, hj, hvj, (⟨hjs, hvH⟩ | ⟨hjs, hvH⟩)⟩ := side _ hv
      · have hpos := (crossBonds_pos M hx (show M.atom x ∈ ({b} : Finset V) by simp [hu])
          (show M.atom (M.mate x) ∈ Dt.sp[j] from hLsp j hjs ▸ hvj)).1
        have h0 := spine_adjacent_b Dt hjs hpos
        subst h0
        exfalso; apply hns
        rw [hu, hfb, hfI _ hv]
        have := idxOf_bounds L hAnd 0 hj hvj
        have c0 := hLsz 0 hj
        simp only [offAt, List.take_zero, List.flatMap_nil, List.length_nil] at this
        rw [← hA] at this
        simp only [ShortArc, bandW_eq]; omega
      · exact inT2 (Or.inr ⟨hu ▸ bH, hvH⟩)
    -- u interior, v = a
    · obtain ⟨i, hi, hui, (⟨his, huH⟩ | ⟨his, huH⟩)⟩ := side _ hu
      · have hpos := (crossBonds_pos M hx (show M.atom x ∈ Dt.sp[i] from hLsp i his ▸ hui)
          (show M.atom (M.mate x) ∈ ({a} : Finset V) by simp [hv])).1
        have hlast := spine_adjacent_a Dt his hpos
        have hne : Dt.sp ≠ [] := List.ne_nil_of_length_pos (by omega)
        refine Finset.mem_union_left _ ?_
        simp only [T1, dif_pos hne]
        refine Finset.mem_filter.mpr ⟨hxb, Or.inl ⟨?_, by simp [hv]⟩⟩
        rw [List.getLast_eq_getElem]
        have : Dt.sp.length - 1 = i := by omega
        simp only [this]
        exact hLsp i his ▸ hui
      · exact inT2 (Or.inl ⟨huH, hv ▸ aH⟩)
    -- u interior, v = b
    · obtain ⟨i, hi, hui, (⟨his, huH⟩ | ⟨his, huH⟩)⟩ := side _ hu
      · have hpos := (crossBonds_pos M hx (show M.atom x ∈ Dt.sp[i] from hLsp i his ▸ hui)
          (show M.atom (M.mate x) ∈ ({b} : Finset V) by simp [hv])).2
        have h0 := spine_adjacent_b Dt his hpos
        subst h0
        exfalso; apply hns
        rw [hv, hfb, hfI _ hu]
        have := idxOf_bounds L hAnd 0 hi hui
        have c0 := hLsz 0 hi
        simp only [offAt, List.take_zero, List.flatMap_nil, List.length_nil] at this
        rw [← hA] at this
        simp only [ShortArc, bandW_eq]; omega
      · exact inT2 (Or.inl ⟨huH, hv ▸ bH⟩)
    -- both interior
    · obtain ⟨i, hi, hui, hsi⟩ := side _ hu
      obtain ⟨j, hj, hvj, hsj⟩ := side _ hv
      rcases hsi with ⟨his, huH⟩ | ⟨his, huH⟩ <;> rcases hsj with ⟨hjs, hvH⟩ | ⟨hjs, hvH⟩
      · have hpos := (crossBonds_pos M hx (show M.atom x ∈ Dt.sp[i] from hLsp i his ▸ hui)
          (show M.atom (M.mate x) ∈ Dt.sp[j] from hLsp j hjs ▸ hvj)).1
        obtain ⟨h1, h2⟩ := spine_adjacent Dt his hjs hpos
        exfalso; apply hns
        rw [hfI _ hu, hfI _ hv]
        exact shortI i j hi hj hui hvj h1 h2
      · exact inT2 (Or.inr ⟨huH, hvH⟩)
      · exact inT2 (Or.inl ⟨huH, hvH⟩)
      · have hpos := (crossBonds_pos M hx
          (show M.atom x ∈ Dt.pd[i - Dt.sp.length]'(by omega) from hLpd i hi his ▸ hui)
          (show M.atom (M.mate x) ∈ Dt.pd[j - Dt.sp.length]'(by omega) from hLpd j hj hjs ▸ hvj)).1
        obtain ⟨h1, h2⟩ := pendant_adjacent Dt (by omega) (by omega) hpos
        exfalso; apply hns
        rw [hfI _ hu, hfI _ hv]
        exact shortI i j hi hj hui hvj (by omega) (by omega)
  -- count
  unfold WaveTurbulence.ClassCount.groupArcs
  rw [Multiset.filter_map, Multiset.card_map, ← Finset.filter_val, Finset.card_val,
    Finset.filter_filter]
  calc _ ≤ (T1 ∪ T2).card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨-, ⟨hx1, hx2⟩, hx3⟩ := Finset.mem_filter.mp hx
        exact key x hx1 hx2 hx3
    _ ≤ T1.card + T2.card := Finset.card_union_le _ _
    _ ≤ 4 := by omega

/-- **Every block with the Theorem 6 spine data and pieces of at most three atoms has a band labelling**: joints `0`
(upper) and `1` (lower), a bijection onto `0, …, |S| − 1`, and a band-admissible arc multiset. -/
theorem exists_band_labelling (Dt : SpineData M S a b) (hB : M.IsBlock S a b) (hM : M.IsMolecule)
    (hpsz : ∀ P ∈ M.pieces S a b, P.card ≤ 3) :
    ∃ f : V → ℕ, Set.InjOn f S ∧ S.image f = range S.card ∧ f a = 0 ∧ f b = 1 ∧
      BandAdmissible S.card (WaveTurbulence.ClassCount.groupArcs M S f) := by
  classical
  set L := Dt.sp ++ Dt.pd with hL
  set A := atomList L with hA
  set I := (S.erase a).erase b with hI
  have hab : a ≠ b := hB.2.2.2.1
  have haS : a ∈ S := hB.2.1
  have hbS : b ∈ S := hB.2.2.1
  have hLp : ∀ P ∈ L, P ∈ M.pieces S a b := fun P hP => Dt.pieces ▸ List.mem_toFinset.mpr hP
  have hLsz : ∀ (i : ℕ) (hi : i < L.length), L[i].card ≤ 3 := fun i hi => hpsz _ (hLp _ (List.getElem_mem hi))
  have hAnd : A.Nodup := by
    refine List.nodup_flatMap.mpr ⟨fun P _ => Finset.nodup_toList P, ?_⟩
    refine List.Nodup.pairwise_of_forall_ne Dt.nodup fun P hP Q hQ hne => ?_
    have hd := pieces_disjoint M (hLp P hP) (hLp Q hQ) hne
    exact fun z hz hz' => Finset.disjoint_left.mp hd (Finset.mem_toList.mp hz) (Finset.mem_toList.mp hz')
  have hmemA : ∀ v, v ∈ A ↔ v ∈ I := by
    intro v
    constructor
    · intro hv
      obtain ⟨P, hP, hvP⟩ := List.mem_flatMap.mp hv
      exact pieces_subset M (hLp P hP) (Finset.mem_toList.mp hvP)
    · intro hv
      obtain ⟨P, hP, hvP⟩ := exists_piece M hv
      have : P ∈ L := List.mem_toFinset.mp (Dt.pieces.symm ▸ hP)
      exact List.mem_flatMap.mpr ⟨P, this, Finset.mem_toList.mpr hvP⟩
  have hAlen : A.length = I.card := by
    rw [← List.toFinset_card_of_nodup hAnd]
    congr 1
    ext v
    simp [hmemA]
  -- locations
  have hloc : ∀ v ∈ I, ∃ i, ∃ hi : i < L.length, v ∈ L[i] := by
    intro v hv
    obtain ⟨P, hP, hvP⟩ := exists_piece M hv
    have : P ∈ L := List.mem_toFinset.mp (Dt.pieces.symm ▸ hP)
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp this
    exact ⟨i, hi, hvP⟩
  have haI : a ∉ I := by simp [hI]
  have hbI : b ∉ I := by simp [hI]
  set f := bandLabel a b A with hf
  have hfa : f a = 0 := by simp [hf, bandLabel]
  have hfb : f b = 1 := by simp [hf, bandLabel, Ne.symm hab]
  have hfI : ∀ v ∈ I, f v = A.idxOf v + 2 := by
    intro v hv
    have hva : v ≠ a := fun h => haI (h ▸ hv)
    have hvb : v ≠ b := fun h => hbI (h ▸ hv)
    simp [hf, bandLabel, hva, hvb]
  have hidx : ∀ v ∈ I, A.idxOf v < I.card := fun v hv => hAlen ▸ List.idxOf_lt_length_of_mem ((hmemA v).mpr hv)
  have hSsplit : ∀ v ∈ S, v = a ∨ v = b ∨ v ∈ I := by
    intro v hv
    by_cases h1 : v = a
    · exact Or.inl h1
    · by_cases h2 : v = b
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (by simp [hI, h1, h2, hv]))
  have hScard : S.card = I.card + 2 := by
    have hbS' : b ∈ S.erase a := mem_erase.mpr ⟨Ne.symm hab, hbS⟩
    rw [hI, card_erase_of_mem hbS', card_erase_of_mem haS]
    have : 2 ≤ S.card := by
      have := card_le_card (show ({a, b} : Finset V) ⊆ S by
        intro v hv; rcases mem_insert.mp hv with rfl | hv
        · exact haS
        · rw [mem_singleton.mp hv]; exact hbS)
      rwa [card_pair hab] at this
    omega
  have hinj : Set.InjOn f S := by
    intro u hu v hv huv
    rcases hSsplit u hu with rfl | rfl | huI <;> rcases hSsplit v hv with rfl | rfl | hvI
    all_goals first
      | rfl
      | (simp only [hfa, hfb] at huv; omega)
      | (rw [hfI _ hvI] at huv; simp only [hfa, hfb] at huv; omega)
      | (rw [hfI _ huI] at huv; simp only [hfa, hfb] at huv; omega)
      | skip
    rw [hfI _ huI, hfI _ hvI] at huv
    have := List.idxOf_inj (l := A) ((hmemA u).mpr huI) |>.mp (by omega : A.idxOf u = A.idxOf v)
    exact this
  have hlt : ∀ v ∈ S, f v < S.card := by
    intro v hv
    rcases hSsplit v hv with rfl | rfl | hvI
    · rw [hfa]; omega
    · rw [hfb]; omega
    · rw [hfI v hvI]; have := hidx v hvI; omega
  have himg : S.image f = range S.card := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
    · obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
      exact mem_range.mpr (hlt v hv)
    · rw [card_range, card_image_of_injOn hinj]
  refine ⟨f, hinj, himg, hfa, hfb, ?_, ?_, ?_⟩
  · -- endpoints in range
    intro q hq
    unfold WaveTurbulence.ClassCount.groupArcs at hq
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hq
    have hx' := (Finset.mem_filter.mp (Finset.mem_val.mp hx)).2
    exact ⟨hlt _ hx'.2.1, hlt _ hx'.2.2⟩
  · exact long_count_le Dt hab haS hbS hLp hLsz hAnd hloc haI hbI hfa hfb hfI
  · exact short_mult_le hM hB.1 hinj

end Labelling

end WaveTurbulence.GammaLow.Famc.ClassCount
