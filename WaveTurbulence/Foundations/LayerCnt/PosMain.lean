/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.PosDefs
public import WaveTurbulence.Foundations.LayerCnt.ChainLower
import Mathlib.Tactic

/-! # Rail-position cuts of every expansion (TARGET layervine, L1531)

For a base slot whose two bonds are an edge cut `K0` of the template (`PosA`, `PosB`), and every position
`0 ≤ j ≤ k` of the inserted ladder, the set `K` (positions on the `K0`-side of the cut, base atoms in `K0`) is a cut of
the expansion with two single crossing bonds: the two rail bonds at position `j`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open WaveTurbulence.Vine

theorem expand_kcutPos (X : VineType) (ks : List ℕ) (hk : ks.length = X.template.slots.length)
    (c : ℕ) (hc : c < X.template.slots.length) {K0 : List ℕ}
    (hA : PosA X.template (X.template.slots[c]'hc) K0) (hB : PosB X.template c (X.template.slots[c]'hc) K0)
    (j : ℕ) (hj : j ≤ ks[c]'(by omega)) :
    ∃ K : ℕ → Prop,
      IsKCut (X.expand ks) K
        (orientE (kap K0 (X.template.slots[c]'hc).1.2)
          (railEdge (X.template.slots[c]'hc).1.1 (X.template.slots[c]'hc).1.2 (ks[c]'(by omega))
            (fun i => X.template.n + 2 * (ks.take c).sum + i) j))
        (orientE (kap K0 (X.template.slots[c]'hc).1.2)
          (railEdge (X.template.slots[c]'hc).2.1 (X.template.slots[c]'hc).2.2 (ks[c]'(by omega))
            (fun i => X.template.n + 2 * (ks.take c).sum + ks[c]'(by omega) + i) j)) ∧
      (∀ v < X.template.n, (K v ↔ v ∈ K0)) ∧
      (∀ i < ks[c]'(by omega),
        (K (X.template.n + 2 * (ks.take c).sum + i) ↔
          posVal j (kap K0 (X.template.slots[c]'hc).1.1) (kap K0 (X.template.slots[c]'hc).1.2) (i + 1) = 2) ∧
        (K (X.template.n + 2 * (ks.take c).sum + ks[c]'(by omega) + i) ↔
          posVal j (kap K0 (X.template.slots[c]'hc).1.1) (kap K0 (X.template.slots[c]'hc).1.2) (i + 1) = 2)) := by
  obtain ⟨hn2, hbdd, hsl⟩ := baseOK X
  have hdist := slotsDistinct X
  set T0 := X.template with hT0
  set F : VineTemplate → ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ → VineTemplate := fun U sk => insertRungs U sk.1 sk.2 with hF
  set xs := T0.slots.zip ks with hxs
  have hcl : c < xs.length := by simp [hxs, List.length_zip, hk, hc]
  have hckl : c < ks.length := by omega
  set s := T0.slots[c]'hc with hs
  set kc := ks[c]'hckl with hkc
  have hxc : xs[c]'hcl = (s, kc) := by simp [hxs, hs, hkc, List.getElem_zip]
  have hloc : xs = xs.take c ++ (xs[c]'hcl) :: xs.drop (c + 1) := by
    rw [← List.drop_eq_getElem_cons hcl, List.take_append_drop]
  have hexp : X.expand ks = (xs.drop (c + 1)).foldl F (insertRungs ((xs.take c).foldl F T0) s kc) := by
    unfold VineType.expand
    change xs.foldl F T0 = _
    conv_lhs => rw [hloc]
    rw [List.foldl_append, List.foldl_cons, hxc]
  set P := (xs.take c).foldl F T0 with hP
  have hPn : P.n = T0.n + 2 * (ks.take c).sum := by
    rw [hP, fold_insertRungs_atoms]
    have : (xs.take c).map Prod.snd = ks.take c := by
      rw [List.map_take, hxs, List.map_snd_zip (by omega)]
    rw [this]
  obtain ⟨hrange, hcutS, hx0, hy0, hxy0⟩ := hA
  obtain ⟨hside, hsxy, hsxy', hcls, hss1, hss2, hsb1, hsb2⟩ := hB
  set κ := kap K0 with hκ
  set c0 := κ s.1.1 with hc0
  set c1 := κ s.1.2 with hc1
  have hκle : ∀ v, κ v ≤ 2 := fun v => kap_le K0 v
  have hκne : ∀ v, κ v ≠ 1 := fun v => kap_ne_one K0 v
  have hcc : (c0 = 0 ∧ c1 = 2) ∨ (c0 = 2 ∧ c1 = 0) := by
    have := hκle s.1.1; have := hκle s.1.2; have := hκne s.1.1; have := hκne s.1.2; omega
  have hsm : s ∈ T0.slots := List.getElem_mem hc
  obtain ⟨hsend, hsc1, hsc2⟩ := hsl s hsm
  have hx : s.1.1 < T0.n := hsend _ (by simp [slotEnds])
  have hy : s.1.2 < T0.n := hsend _ (by simp [slotEnds])
  have hx' : s.2.1 < T0.n := hsend _ (by simp [slotEnds])
  have hy' : s.2.2 < T0.n := hsend _ (by simp [slotEnds])
  -- other slots lie on one side
  have hidx : ∀ j (hj : j < xs.length), j ≠ c → Sides2 κ (slotEnds (xs[j]'hj).1) := by
    intro j hj hjc
    have hjs : j < T0.slots.length := by
      have : xs.length ≤ T0.slots.length := by simp [hxs, List.length_zip]
      omega
    have : (xs[j]'hj).1 = T0.slots[j]'hjs := by simp [hxs, List.getElem_zip]
    rw [this]
    have := hside j hjs hjc
    rwa [List.getD_eq_getElem _ _ hjs] at this
  have hpre : ∀ sk ∈ xs.take c, Sides2 κ (slotEnds sk.1) := by
    intro sk hsk
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hsk
    have hj' : j < c := by simp at hj; omega
    have hjx : j < xs.length := by simp at hj; omega
    have : (xs.take c)[j]'hj = xs[j]'hjx := by simp
    rw [this]
    exact hidx j hjx (by omega)
  have hpost : ∀ sk ∈ xs.drop (c + 1), Sides2 κ (slotEnds sk.1) := by
    intro sk hsk
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hsk
    have hjx : c + 1 + j < xs.length := by simp at hj; omega
    have : (xs.drop (c + 1))[j]'hj = xs[c + 1 + j]'hjx := by simp
    rw [this]
    exact hidx _ hjx (by omega)
  have hends_xs : ∀ sk ∈ xs, ∀ v ∈ slotEnds sk.1, v < T0.n := fun sk hsk =>
    (hsl _ (List.of_mem_zip hsk).1).1
  have hcnt_xs : ∀ sk ∈ xs, T0.bonds.count sk.1.1 ≤ 1 ∧ T0.bonds.count sk.1.2 ≤ 1 := fun sk hsk =>
    ⟨(hsl _ (List.of_mem_zip hsk).1).2.1, (hsl _ (List.of_mem_zip hsk).1).2.2⟩
  -- the other slot members differ from the slot `c`
  have hne_mem : ∀ sk ∈ xs.take c ++ xs.drop (c + 1), s.1 ≠ sk.1.1 ∧ s.1 ≠ sk.1.2 ∧ s.2 ≠ sk.1.1 ∧ s.2 ≠ sk.1.2 := by
    intro sk hsk
    rcases List.mem_append.mp hsk with h | h
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h
      have hj' : j < c := by simp at hj; omega
      have hjx : j < xs.length := by simp at hj; omega
      have hjs : j < T0.slots.length := by
        have : xs.length ≤ T0.slots.length := by simp [hxs, List.length_zip]
        omega
      have := slotsDistinct_getElem hdist hc hjs (by omega)
      have e : ((xs.take c)[j]'hj).1 = T0.slots[j]'hjs := by simp [hxs, List.getElem_zip]
      rw [e]; exact this
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h
      have hjx : c + 1 + j < xs.length := by simp at hj; omega
      have hjs : c + 1 + j < T0.slots.length := by
        have : xs.length ≤ T0.slots.length := by simp [hxs, List.length_zip]
        omega
      have := slotsDistinct_getElem hdist hc hjs (by omega)
      have e : ((xs.drop (c + 1))[j]'hj).1 = T0.slots[c + 1 + j]'hjs := by simp [hxs, List.getElem_zip]
      rw [e]; exact this
  have hCutOnS : CutOn T0.bonds [s.1, s.2] κ := fun e he hn =>
    hcutS e he (fun h => hn (by simp [h])) (fun h => hn (by simp [h]))
  obtain ⟨σp, hp1, hp2, hp3, hp4⟩ := fold_ext (xs.take c) T0.n T0 [s.1, s.2] κ le_rfl hbdd
    (fun sk h => hcnt_xs sk (List.mem_of_mem_take h))
    (fun sk h => ⟨hends_xs sk (List.mem_of_mem_take h), hpre sk h⟩) hCutOnS hκle
  have hPb := fold_bdd (xs.take c) T0.n T0 le_rfl hbdd (fun sk h => hends_xs sk (List.mem_of_mem_take h))
  have hPc : ∀ e : ℕ × ℕ, e.1 < T0.n → e.2 < T0.n → P.bonds.count e ≤ T0.bonds.count e := fun e h1 h2 =>
    fold_count (xs.take c) T0.n T0 e h1 h2 le_rfl (fun sk h => hends_xs sk (List.mem_of_mem_take h))
  have hPge : T0.n ≤ P.n := by rw [hPn]; omega
  have hPends : ∀ v ∈ slotEnds s, v < P.n := fun v hv => lt_of_lt_of_le (hsend v hv) hPge
  have hc1' : P.bonds.count s.1 ≤ 1 := (hPc s.1 hx hy).trans hsc1
  have hc2' : P.bonds.count s.2 ≤ 1 := (hPc s.2 hx' hy').trans hsc2
  set ρ := posσ P.n kc j c0 c1 σp with hρ
  have hρle : ∀ v, ρ v ≤ 2 := posσ_le (by omega) (by omega) hp2
  have hρold : ∀ v < T0.n, ρ v = κ v := fun v hv => by
    rw [hρ, posσ_old (by omega), hp1 v hv]
  set e1 := railEdge s.1.1 s.1.2 kc (fun i => P.n + i) j with he1
  set e2 := railEdge s.2.1 s.2.2 kc (fun i => P.n + kc + i) j with he2
  set Ej : List (ℕ × ℕ) := [e1, (e1.2, e1.1), e2, (e2.2, e2.1)] with hEj
  have hTm : (insertRungs P s kc).n = P.n + 2 * kc := insertRungs_atoms _ _ _
  have hρcut : CutOn (insertRungs P s kc).bonds Ej ρ := by
    by_cases hkc0 : kc = 0
    · have hj0 : j = 0 := by omega
      have hTmP : insertRungs P s kc = P := by rw [hkc0]; exact insertRungs_zero _ _
      have hρeq : ρ = σp := by rw [hρ, hkc0, posσ_zero]
      have he1s : e1 = s.1 := by simp [he1, railEdge, railSeq, hkc0, hj0]
      have he2s : e2 = s.2 := by simp [he2, railEdge, railSeq, hkc0, hj0]
      rw [hTmP, hρeq]
      intro e he hn
      apply hp4 e he
      intro hmem
      apply hn
      rcases List.mem_cons.mp hmem with h | h
      · rw [h, ← he1s]; simp [hEj]
      · rw [List.mem_singleton.mp h, ← he2s]; simp [hEj]
    · exact pos_cuton hj hkc0 hc1' hc2' hPb hPends hcc
        ⟨by rw [hp1 _ hx], by rw [hp1 _ hx', ← hx0]⟩ ⟨by rw [hp1 _ hy], by rw [hp1 _ hy', ← hy0]⟩ hp4
  have hbddTm := bdd_insert (s := s) (k := kc) hPends hPb
  obtain ⟨σf, hf1, hf2, hf3, hf4⟩ := fold_ext (xs.drop (c + 1)) T0.n (insertRungs P s kc) Ej ρ
    (by omega) hbddTm
    (fun sk hsk => by
      have hm : sk ∈ xs := List.mem_of_mem_drop hsk
      have hh := hends_xs sk hm
      have hA : sk.1.1.1 < T0.n ∧ sk.1.1.2 < T0.n :=
        ⟨hh _ (by simp [slotEnds]), hh _ (by simp [slotEnds])⟩
      have hB : sk.1.2.1 < T0.n ∧ sk.1.2.2 < T0.n :=
        ⟨hh _ (by simp [slotEnds]), hh _ (by simp [slotEnds])⟩
      exact ⟨(count_insert_le (s := s) (k := kc) ⟨by omega, by omega⟩).trans
          ((hPc _ hA.1 hA.2).trans (hcnt_xs sk hm).1),
        (count_insert_le (s := s) (k := kc) ⟨by omega, by omega⟩).trans
          ((hPc _ hB.1 hB.2).trans (hcnt_xs sk hm).2)⟩)
    (fun sk hsk => by
      have hm : sk ∈ xs := List.mem_of_mem_drop hsk
      refine ⟨hends_xs sk hm, ?_⟩
      have := hpost sk hsk
      intro ⟨⟨v, hv, hv0⟩, ⟨w, hw, hw2⟩⟩
      apply this
      exact ⟨⟨v, hv, by rw [← hρold v (hends_xs sk hm v hv)]; exact hv0⟩,
        ⟨w, hw, by rw [← hρold w (hends_xs sk hm w hw)]; exact hw2⟩⟩)
    hρcut hρle
  have hbddF := fold_bdd (xs.drop (c + 1)) T0.n (insertRungs P s kc) (by omega) hbddTm
    (fun sk hsk => hends_xs sk (List.mem_of_mem_drop hsk))
  have hnF : (insertRungs P s kc).n ≤ (X.expand ks).n := by
    rw [hexp, fold_insertRungs_atoms]; omega
  rw [hexp] at hnF ⊢
  set n' := ((xs.drop (c + 1)).foldl F (insertRungs P s kc)).n with hn'
  -- values
  have hρne1 : ∀ v, v < P.n + 2 * kc → ρ v ≠ 1 := by
    intro v hv
    by_cases hvP : v < P.n
    · rw [hρ, posσ_old hvP]
      by_cases hv0 : v < T0.n
      · rw [hp1 v hv0]; exact hκne v
      · exact hp3 v (by omega) hvP
    · rw [hρ]; unfold posσ
      rw [if_neg (by omega)]
      dsimp only
      split_ifs <;> omega
  have hne1 : ∀ v, v < n' → σf v ≠ 1 := by
    intro v hv
    by_cases hvT : v < (insertRungs P s kc).n
    · rw [hf1 v hvT]; exact hρne1 v (by omega)
    · exact hf3 v (by omega) hv
  have hσle : ∀ v, σf v ≤ 2 := hf2
  -- values on the crossing edges
  have hrs1 : ∀ m ≤ kc + 1, ρ (railSeq s.1.1 s.1.2 kc (fun i => P.n + i) m) = posVal j c0 c1 m := by
    intro m hm
    exact railSeq_posVal (n := P.n) (τ := σp) (c₀ := c0) (c₁ := c1) (j := j) (g := fun i => P.n + i)
      (fun i hi => by rw [posσ_u hi]; unfold posVal; rfl)
      (by rw [posσ_old (by omega), hp1 _ hx]) (by rw [posσ_old (by omega), hp1 _ hy]) hj hm
  have hrs2 : ∀ m ≤ kc + 1, ρ (railSeq s.2.1 s.2.2 kc (fun i => P.n + kc + i) m) = posVal j c0 c1 m := by
    intro m hm
    exact railSeq_posVal (n := P.n) (τ := σp) (c₀ := c0) (c₁ := c1) (j := j) (g := fun i => P.n + kc + i)
      (fun i hi => by rw [posσ_v hi]; unfold posVal; rfl)
      (by rw [posσ_old (by omega), hp1 _ hx', ← hx0]) (by rw [posσ_old (by omega), hp1 _ hy', ← hy0]) hj hm
  have hlt1 : ∀ m ≤ kc + 1, railSeq s.1.1 s.1.2 kc (fun i => P.n + i) m < P.n + 2 * kc := by
    intro m hm
    rcases railSeq_cases (a := s.1.1) (b := s.1.2) (g := fun i => P.n + i) hm with h | h | ⟨i, hi, h⟩
    · rw [h]; omega
    · rw [h]; omega
    · rw [h]; omega
  have hlt2 : ∀ m ≤ kc + 1, railSeq s.2.1 s.2.2 kc (fun i => P.n + kc + i) m < P.n + 2 * kc := by
    intro m hm
    rcases railSeq_cases (a := s.2.1) (b := s.2.2) (g := fun i => P.n + kc + i) hm with h | h | ⟨i, hi, h⟩
    · rw [h]; omega
    · rw [h]; omega
    · rw [h]; omega
  have hσ1a : σf e1.1 = c0 := by
    have := hlt1 j (by omega)
    show σf (railSeq s.1.1 s.1.2 kc (fun i => P.n + i) j) = c0
    rw [hf1 _ (by omega), hrs1 j (by omega)]; unfold posVal; simp
  have hσ1b : σf e1.2 = c1 := by
    have := hlt1 (j + 1) (by omega)
    show σf (railSeq s.1.1 s.1.2 kc (fun i => P.n + i) (j + 1)) = c1
    rw [hf1 _ (by omega), hrs1 (j + 1) (by omega)]; unfold posVal; simp
  have hσ2a : σf e2.1 = c0 := by
    have := hlt2 j (by omega)
    show σf (railSeq s.2.1 s.2.2 kc (fun i => P.n + kc + i) j) = c0
    rw [hf1 _ (by omega), hrs2 j (by omega)]; unfold posVal; simp
  have hσ2b : σf e2.2 = c1 := by
    have := hlt2 (j + 1) (by omega)
    show σf (railSeq s.2.1 s.2.2 kc (fun i => P.n + kc + i) (j + 1)) = c1
    rw [hf1 _ (by omega), hrs2 (j + 1) (by omega)]; unfold posVal; simp
  have he1lt : e1.1 < P.n + 2 * kc ∧ e1.2 < P.n + 2 * kc := ⟨hlt1 j (by omega), hlt1 (j + 1) (by omega)⟩
  have he2lt : e2.1 < P.n + 2 * kc ∧ e2.2 < P.n + 2 * kc := ⟨hlt2 j (by omega), hlt2 (j + 1) (by omega)⟩
  -- facts for kc = 0
  have hk0 : kc = 0 → insertRungs P s kc = P ∧ e1 = s.1 ∧ e2 = s.2 := by
    intro hkc0
    have hj0 : j = 0 := by omega
    refine ⟨by rw [hkc0]; exact insertRungs_zero _ _, ?_, ?_⟩
    · simp [he1, railEdge, railSeq, hkc0, hj0]
    · simp [he2, railEdge, railSeq, hkc0, hj0]
  have hendsTm : ∀ sk ∈ xs.drop (c + 1), ∀ v ∈ slotEnds sk.1, v < (insertRungs P s kc).n := fun sk hsk v hv => by
    have := hends_xs sk (List.mem_of_mem_drop hsk) v hv; omega
  -- membership of the crossing edges
  have hm1 : e1 ∈ ((xs.drop (c + 1)).foldl F (insertRungs P s kc)).bonds := by
    refine fold_mem_bonds (xs.drop (c + 1)) (insertRungs P s kc) e1 ?_ ?_
    · by_cases hkc0 : kc = 0
      · obtain ⟨hT, h1, _⟩ := hk0 hkc0
        rw [hT, h1]
        exact fold_mem_bonds (xs.take c) T0 s.1 hsb1 (fun sk hsk =>
          ⟨(hne_mem sk (List.mem_append_left _ hsk)).1, (hne_mem sk (List.mem_append_left _ hsk)).2.1⟩)
      · simp only [insertRungs, hkc0, ite_false, List.mem_append]
        left; left; right
        rw [rail_eq_map]
        exact List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩
    · intro sk hsk
      by_cases hkc0 : kc = 0
      · obtain ⟨_, h1, _⟩ := hk0 hkc0
        rw [h1]
        exact ⟨(hne_mem sk (List.mem_append_right _ hsk)).1, (hne_mem sk (List.mem_append_right _ hsk)).2.1⟩
      · obtain ⟨i, hi, hh⟩ := edge_has_new (a := s.1.1) (b := s.1.2) (g := fun i => P.n + i) hkc0 hj
        have hh' := hends_xs sk (List.mem_of_mem_drop hsk)
        have a1 := hh' sk.1.1.1 (by simp [slotEnds])
        have a2 := hh' sk.1.1.2 (by simp [slotEnds])
        have a3 := hh' sk.1.2.1 (by simp [slotEnds])
        have a4 := hh' sk.1.2.2 (by simp [slotEnds])
        constructor
        · intro hh2
          rcases hh with h | h
          · have : e1.1 = sk.1.1.1 := by rw [hh2]
            have h' : e1.1 = P.n + i := h
            omega
          · have : e1.2 = sk.1.1.2 := by rw [hh2]
            have h' : e1.2 = P.n + i := h
            omega
        · intro hh2
          rcases hh with h | h
          · have : e1.1 = sk.1.2.1 := by rw [hh2]
            have h' : e1.1 = P.n + i := h
            omega
          · have : e1.2 = sk.1.2.2 := by rw [hh2]
            have h' : e1.2 = P.n + i := h
            omega
  have hm2 : e2 ∈ ((xs.drop (c + 1)).foldl F (insertRungs P s kc)).bonds := by
    refine fold_mem_bonds (xs.drop (c + 1)) (insertRungs P s kc) e2 ?_ ?_
    · by_cases hkc0 : kc = 0
      · obtain ⟨hT, _, h2⟩ := hk0 hkc0
        rw [hT, h2]
        exact fold_mem_bonds (xs.take c) T0 s.2 hsb2 (fun sk hsk =>
          ⟨(hne_mem sk (List.mem_append_left _ hsk)).2.2.1, (hne_mem sk (List.mem_append_left _ hsk)).2.2.2⟩)
      · simp only [insertRungs, hkc0, ite_false, List.mem_append]
        left; right
        rw [rail_eq_map]
        exact List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩
    · intro sk hsk
      by_cases hkc0 : kc = 0
      · obtain ⟨_, _, h2⟩ := hk0 hkc0
        rw [h2]
        exact ⟨(hne_mem sk (List.mem_append_right _ hsk)).2.2.1, (hne_mem sk (List.mem_append_right _ hsk)).2.2.2⟩
      · obtain ⟨i, hi, hh⟩ := edge_has_new (a := s.2.1) (b := s.2.2) (g := fun i => P.n + kc + i) hkc0 hj
        have hh' := hends_xs sk (List.mem_of_mem_drop hsk)
        have a1 := hh' sk.1.1.1 (by simp [slotEnds])
        have a2 := hh' sk.1.1.2 (by simp [slotEnds])
        have a3 := hh' sk.1.2.1 (by simp [slotEnds])
        have a4 := hh' sk.1.2.2 (by simp [slotEnds])
        constructor
        · intro hh2
          rcases hh with h | h
          · have : e2.1 = sk.1.1.1 := by rw [hh2]
            have h' : e2.1 = P.n + kc + i := h
            omega
          · have : e2.2 = sk.1.1.2 := by rw [hh2]
            have h' : e2.2 = P.n + kc + i := h
            omega
        · intro hh2
          rcases hh with h | h
          · have : e2.1 = sk.1.2.1 := by rw [hh2]
            have h' : e2.1 = P.n + kc + i := h
            omega
          · have : e2.2 = sk.1.2.2 := by rw [hh2]
            have h' : e2.2 = P.n + kc + i := h
            omega
  -- singleness
  have hsg1 : SymSingle ((xs.drop (c + 1)).foldl F (insertRungs P s kc)) e1 := by
    have h0 : SymSingle (insertRungs P s kc) e1 := by
      by_cases hkc0 : kc = 0
      · obtain ⟨hT, h1, _⟩ := hk0 hkc0
        rw [hT, h1]
        unfold SymSingle at hss1 ⊢
        exact (fold_symcount_le (xs.take c) T0.n T0 s.1 hx hy le_rfl
          (fun sk h => hends_xs sk (List.mem_of_mem_take h))).trans hss1
      · exact pos_symsingle1 hkc0 hj hPb hPends hsxy
    unfold SymSingle at h0 ⊢
    exact (fold_symcount_le (xs.drop (c + 1)) (insertRungs P s kc).n (insertRungs P s kc) e1
      (by omega) (by omega) le_rfl hendsTm).trans h0
  have hsg2 : SymSingle ((xs.drop (c + 1)).foldl F (insertRungs P s kc)) e2 := by
    have h0 : SymSingle (insertRungs P s kc) e2 := by
      by_cases hkc0 : kc = 0
      · obtain ⟨hT, _, h2⟩ := hk0 hkc0
        rw [hT, h2]
        unfold SymSingle at hss2 ⊢
        exact (fold_symcount_le (xs.take c) T0.n T0 s.2 hx' hy' le_rfl
          (fun sk h => hends_xs sk (List.mem_of_mem_take h))).trans hss2
      · exact pos_symsingle2 hkc0 hj hPb hPends hsxy'
    unfold SymSingle at h0 ⊢
    exact (fold_symcount_le (xs.drop (c + 1)) (insertRungs P s kc).n (insertRungs P s kc) e2
      (by omega) (by omega) le_rfl hendsTm).trans h0
  -- the two crossing classes differ
  have hne12 : s(e1.1, e1.2) ≠ s(e2.1, e2.2) := by
    by_cases hkc0 : kc = 0
    · obtain ⟨_, h1, h2⟩ := hk0 hkc0
      rw [h1, h2]; exact hcls
    · intro h
      obtain ⟨i, hi, hh⟩ := edge_has_new (a := s.1.1) (b := s.1.2) (g := fun i => P.n + i) hkc0 hj
      have hc2 : ∀ m ≤ kc + 1, railSeq s.2.1 s.2.2 kc (fun i => P.n + kc + i) m < P.n ∨
          P.n + kc ≤ railSeq s.2.1 s.2.2 kc (fun i => P.n + kc + i) m := by
        intro m hm
        rcases railSeq_cases (a := s.2.1) (b := s.2.2) (g := fun i => P.n + kc + i) hm with h | h | ⟨i, hi, h⟩
        · left; rw [h]; omega
        · left; rw [h]; omega
        · right; rw [h]; omega
      have h21 : e2.1 < P.n ∨ P.n + kc ≤ e2.1 := hc2 j (by omega)
      have h22 : e2.2 < P.n ∨ P.n + kc ≤ e2.2 := hc2 (j + 1) (by omega)
      have hh' : e1.1 = P.n + i ∨ e1.2 = P.n + i := hh
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hnj : ∀ v, (v < n' ∧ σf v = 2) → 2 ≤ v ∧ v < n' := by
    rintro v ⟨hv, hv2⟩
    refine ⟨?_, hv⟩
    by_cases hv0 : v < T0.n
    · rw [hf1 v (by omega), hρold v hv0] at hv2
      have : v ∈ K0 := by by_contra hcn; simp [hκ, kap, hcn] at hv2
      exact (hrange v this).1
    · omega
  -- the final statement
  rw [← hPn]
  refine ⟨fun v => v < n' ∧ σf v = 2, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hnj⟩, ?_, ?_⟩
  · -- cross
    intro e he hc1' hc2'
    have hnE : e ∉ Ej := by
      intro hE'
      simp only [hEj, List.mem_cons, List.not_mem_nil, or_false] at hE'
      rcases hE' with h | h | h | h
      · exact hc1' (by rw [orientE_class, h])
      · exact hc1' (by rw [orientE_class, h]; exact Sym2.eq_swap)
      · exact hc2' (by rw [orientE_class, h])
      · exact hc2' (by rw [orientE_class, h]; exact Sym2.eq_swap)
    have hb := hbddF e he
    have hnc := hf4 e he hnE
    have h1 := hne1 e.1 hb.1
    have h2 := hne1 e.2 hb.2
    have := hσle e.1
    have := hσle e.2
    unfold Crosses at hnc
    constructor
    · rintro ⟨_, hh⟩; refine ⟨hb.2, ?_⟩; omega
    · rintro ⟨_, hh⟩; refine ⟨hb.1, ?_⟩; omega
  · unfold orientE; split_ifs
    · exact Or.inr hm1
    · exact Or.inl hm1
  · unfold orientE; split_ifs
    · exact Or.inr hm2
    · exact Or.inl hm2
  · unfold SymSingle at hsg1 ⊢; rw [orientE_class]; exact hsg1
  · unfold SymSingle at hsg2 ⊢; rw [orientE_class]; exact hsg2
  · rw [orientE_class, orientE_class]; exact hne12
  · -- orientation of the first crossing edge
    have hn1 : e1.1 < n' ∧ e1.2 < n' := ⟨by omega, by omega⟩
    have hv1 : σf e1.1 = c0 := hσ1a
    have hv2 : σf e1.2 = c1 := hσ1b
    unfold orientE
    split_ifs with hc
    · exact ⟨⟨hn1.2, by rw [hv2, hc]⟩, fun h => by have := h.2; rw [hv1] at this; omega⟩
    · exact ⟨⟨hn1.1, by rw [hv1]; omega⟩, fun h => by have := h.2; rw [hv2] at this; omega⟩
  · have hn1 : e2.1 < n' ∧ e2.2 < n' := ⟨by omega, by omega⟩
    have hv1 : σf e2.1 = c0 := hσ2a
    have hv2 : σf e2.2 = c1 := hσ2b
    unfold orientE
    split_ifs with hc
    · exact ⟨⟨hn1.2, by rw [hv2, hc]⟩, fun h => by have := h.2; rw [hv1] at this; omega⟩
    · exact ⟨⟨hn1.1, by rw [hv1]; omega⟩, fun h => by have := h.2; rw [hv2] at this; omega⟩
  · intro v hv
    show (v < n' ∧ σf v = 2) ↔ v ∈ K0
    have hv' : v < T0.n := hv
    have hvT : v < (insertRungs P s kc).n := by rw [hTm]; omega
    have hvn : v < n' := by omega
    rw [hf1 v hvT, hρold v hv']
    constructor
    · rintro ⟨_, hh⟩
      by_contra hcn; simp [hκ, kap, hcn] at hh
    · intro hvK
      exact ⟨hvn, by simp [hκ, kap, hvK]⟩
  · intro i hi
    have hvl : P.n + i < (insertRungs P s kc).n := by omega
    have hvl2 : P.n + kc + i < (insertRungs P s kc).n := by omega
    constructor
    · show (P.n + i < n' ∧ σf (P.n + i) = 2) ↔ _
      rw [hf1 _ hvl, hρ, posσ_u hi]
      unfold posVal
      exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    · show (P.n + kc + i < n' ∧ σf (P.n + kc + i) = 2) ↔ _
      rw [hf1 _ hvl2, hρ, posσ_v hi]
      unfold posVal
      exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

end WaveTurbulence.LayerCnt
