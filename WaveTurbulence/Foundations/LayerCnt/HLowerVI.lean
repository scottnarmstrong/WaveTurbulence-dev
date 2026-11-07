/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.HLower
import Mathlib.Tactic

/-! # The lower layer bound for vines (VI), (VII), (VIII) (TARGET layervine, L1531)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open WaveTurbulence WaveTurbulence.Vine TTree
variable {w : ℕ}

theorem good_atom {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} {R : VineRealization M X S a b} {f : V → ℕ} {q : ℕ}
    (hgood : ∀ z ∈ S, ∀ g, g ∈ (X.expand R.k).groups → GoodGroup X R.k g → R.f z ∈ g → q ≤ f z)
    {z : V} (hz : z ∈ S) {g : List ℕ} (hg : g ∈ X.template.groups) (hcut : CutG X.template g)
    (hv : R.f z ∈ g) : q ≤ f z :=
  hgood z hz g (base_group_mem_expand X R.k hg) (Or.inl ⟨hg, hcut⟩) hv

theorem hlower_VI {G : Garden w} {f : GBranch G.tree → ℕ} {p : ℕ} {Reg : GNode G.tree → Prop}
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : VineRealization G.molecule VineType.VI S a b} (h : PeelCtx G f p Reg VineType.VI S a b R) {q : ℕ}
    (hjoint : ∀ z ∈ S, R.f z < 2 → q ≤ f z)
    (hgood : ∀ z ∈ S, ∀ g, g ∈ (VineType.VI.expand R.k).groups → GoodGroup VineType.VI R.k g →
      R.f z ∈ g → q ≤ f z) : ∀ z ∈ S, q ≤ f z := by
  have hc : 1 < VineType.VI.template.slots.length := by decide
  have hck : 1 < R.k.length := by rw [R.length_eq]; exact hc
  -- the cut at the attachment of `H`
  obtain ⟨KA, hKA, _⟩ := kcut_ext VineType.VI R.k R.length_eq (K0 := [8, 9, 10, 11, 12])
    (e1 := (8, 5)) (e2 := (9, 7)) (by decide +kernel)
  have hQA : ∀ z ∈ S, (R.f z = 8 ∨ R.f z = 9) → q ≤ f z :=
    cut_step' h hKA ⟨[8, 9], base_group_mem_expand _ _ (by decide), by simp, by simp⟩
      (fun z hz hzr => by
        simp only at hzr
        rcases hzr with e | e
        · exact good_atom hgood hz (g := [4, 5]) (by decide) (by decide +kernel) (by simp [e])
        · exact good_atom hgood hz (g := [6, 7]) (by decide) (by decide +kernel) (by simp [e]))
  -- the ladder
  have hs1 : VineType.VI.template.slots[1]'hc = ((8, 10), (9, 11)) := rfl
  have hA : PosA VineType.VI.template (VineType.VI.template.slots[1]'hc) [10, 11, 12] := by
    rw [hs1]; decide +kernel
  have hB : PosB VineType.VI.template 1 (VineType.VI.template.slots[1]'hc) [10, 11, 12] := by
    rw [hs1]; decide +kernel
  have h2 : kap [10, 11, 12] (VineType.VI.template.slots[1]'hc).1.2 = 2 := by rw [hs1]; decide +kernel
  have hxg : ∃ g ∈ VineType.VI.template.groups, (VineType.VI.template.slots[1]'hc).1.1 ∈ g ∧
      (VineType.VI.template.slots[1]'hc).2.1 ∈ g := by
    rw [hs1]; exact ⟨[8, 9], by decide, by decide, by decide⟩
  have hyg : ∃ g ∈ VineType.VI.template.groups, (VineType.VI.template.slots[1]'hc).1.2 ∈ g ∧
      (VineType.VI.template.slots[1]'hc).2.2 ∈ g := by
    rw [hs1]; exact ⟨[10, 11, 12], by decide, by decide, by decide⟩
  have e10 : pos1 VineType.VI R.k 1 hc hck 0 = 8 := by simp [pos1, railSeq, VineType.template]
  have e20 : pos2 VineType.VI R.k 1 hc hck 0 = 9 := by simp [pos2, railSeq, VineType.template]
  have hq0 : ∀ z ∈ S, (R.f z = pos1 VineType.VI R.k 1 hc hck 0 ∨ R.f z = pos2 VineType.VI R.k 1 hc hck 0) →
      q ≤ f z := by
    intro z hz hzr; rw [e10, e20] at hzr; exact hQA z hz hzr
  have hchain := pos_chain_fwd h hc hA hB h2 hxg hyg hq0
  have e1e : pos1 VineType.VI R.k 1 hc hck (R.k[1]'hck + 1) = 10 := by
    simp [pos1, railSeq, VineType.template]
  have e2e : pos2 VineType.VI R.k 1 hc hck (R.k[1]'hck + 1) = 11 := by
    simp [pos2, railSeq, VineType.template]
  have hQD : ∀ z ∈ S, (R.f z = 10 ∨ R.f z = 11) → q ≤ f z := by
    intro z hz hzr
    refine hchain (R.k[1]'hck + 1) le_rfl z hz ?_
    rw [e1e, e2e]; exact hzr
  -- cover
  refine lower_cover R h.hcoh hjoint hgood ?_ ?_
  · intro g hg hncut
    simp only [VineType.template, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact base_witness R (by decide) (by decide : (10 : ℕ) ∈ [10, 11, 12]) (fun z hz hzv => hQD z hz (Or.inl hzv))
    · exact absurd (by decide +kernel) hncut
    · exact absurd (by decide +kernel) hncut
    · exact absurd (by decide +kernel) hncut
    · exact base_witness R (by decide) (by decide : (8 : ℕ) ∈ [8, 9]) (fun z hz hzv => hQA z hz (Or.inl hzv))
    · exact absurd (by decide +kernel) hncut
  · intro c' hc' hncut i hi1 hi2
    have hc3 : c' = 0 ∨ c' = 1 ∨ c' = 2 := by
      have : c' < 3 := hc'; omega
    rcases hc3 with rfl | rfl | rfl
    · exact absurd (show CutS VineType.VI.template 0 (VineType.VI.template.slots[0]'(by decide)) by
        decide +kernel) hncut
    · refine rung_witness R hc hi1 hi2 ?_
      intro z hz hzr
      have hgd : R.k.getD 1 0 = R.k[1]'hck := by simp [List.getD_eq_getElem?_getD, hck]
      rw [hgd] at hi2
      exact hchain i (by omega) z hz hzr
    · exact absurd (show CutS VineType.VI.template 2 (VineType.VI.template.slots[2]'(by decide)) by
        decide +kernel) hncut


theorem hlower_VIII {G : Garden w} {f : GBranch G.tree → ℕ} {p : ℕ} {Reg : GNode G.tree → Prop}
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : VineRealization G.molecule VineType.VIII S a b} (h : PeelCtx G f p Reg VineType.VIII S a b R) {q : ℕ}
    (hjoint : ∀ z ∈ S, R.f z < 2 → q ≤ f z)
    (hgood : ∀ z ∈ S, ∀ g, g ∈ (VineType.VIII.expand R.k).groups → GoodGroup VineType.VIII R.k g →
      R.f z ∈ g → q ≤ f z) : ∀ z ∈ S, q ≤ f z := by
  have hc : 1 < VineType.VIII.template.slots.length := by decide
  have hck : 1 < R.k.length := by rw [R.length_eq]; exact hc
  obtain ⟨KA, hKA, _⟩ := kcut_ext VineType.VIII R.k R.length_eq (K0 := [6, 7, 8, 9, 10])
    (e1 := (6, 0)) (e2 := (7, 3)) (by decide +kernel)
  have hQA : ∀ z ∈ S, (R.f z = 6 ∨ R.f z = 7) → q ≤ f z :=
    cut_step' h hKA ⟨[6, 7], base_group_mem_expand _ _ (by decide), by simp, by simp⟩
      (fun z hz hzr => by
        simp only at hzr
        rcases hzr with e | e
        · exact hjoint z hz (by omega)
        · exact good_atom hgood hz (g := [2, 3]) (by decide) (by decide +kernel) (by simp [e]))
  have hs1 : VineType.VIII.template.slots[1]'hc = ((6, 8), (7, 9)) := rfl
  have hA : PosA VineType.VIII.template (VineType.VIII.template.slots[1]'hc) [8, 9, 10] := by
    rw [hs1]; decide +kernel
  have hB : PosB VineType.VIII.template 1 (VineType.VIII.template.slots[1]'hc) [8, 9, 10] := by
    rw [hs1]; decide +kernel
  have h2 : kap [8, 9, 10] (VineType.VIII.template.slots[1]'hc).1.2 = 2 := by rw [hs1]; decide +kernel
  have hxg : ∃ g ∈ VineType.VIII.template.groups, (VineType.VIII.template.slots[1]'hc).1.1 ∈ g ∧
      (VineType.VIII.template.slots[1]'hc).2.1 ∈ g := by
    rw [hs1]; exact ⟨[6, 7], by decide, by decide, by decide⟩
  have hyg : ∃ g ∈ VineType.VIII.template.groups, (VineType.VIII.template.slots[1]'hc).1.2 ∈ g ∧
      (VineType.VIII.template.slots[1]'hc).2.2 ∈ g := by
    rw [hs1]; exact ⟨[8, 9, 10], by decide, by decide, by decide⟩
  have e10 : pos1 VineType.VIII R.k 1 hc hck 0 = 6 := by simp [pos1, railSeq, VineType.template]
  have e20 : pos2 VineType.VIII R.k 1 hc hck 0 = 7 := by simp [pos2, railSeq, VineType.template]
  have hq0 : ∀ z ∈ S, (R.f z = pos1 VineType.VIII R.k 1 hc hck 0 ∨ R.f z = pos2 VineType.VIII R.k 1 hc hck 0) →
      q ≤ f z := by
    intro z hz hzr; rw [e10, e20] at hzr; exact hQA z hz hzr
  have hchain := pos_chain_fwd h hc hA hB h2 hxg hyg hq0
  have e1e : pos1 VineType.VIII R.k 1 hc hck (R.k[1]'hck + 1) = 8 := by
    simp [pos1, railSeq, VineType.template]
  have e2e : pos2 VineType.VIII R.k 1 hc hck (R.k[1]'hck + 1) = 9 := by
    simp [pos2, railSeq, VineType.template]
  have hQD : ∀ z ∈ S, (R.f z = 8 ∨ R.f z = 9) → q ≤ f z := by
    intro z hz hzr
    refine hchain (R.k[1]'hck + 1) le_rfl z hz ?_
    rw [e1e, e2e]; exact hzr
  refine lower_cover R h.hcoh hjoint hgood ?_ ?_
  · intro g hg hncut
    simp only [VineType.template, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact base_witness R (by decide) (by decide : (8 : ℕ) ∈ [8, 9, 10]) (fun z hz hzv => hQD z hz (Or.inl hzv))
    · exact absurd (by decide +kernel) hncut
    · exact absurd (by decide +kernel) hncut
    · exact base_witness R (by decide) (by decide : (6 : ℕ) ∈ [6, 7]) (fun z hz hzv => hQA z hz (Or.inl hzv))
  · intro c' hc' hncut i hi1 hi2
    have hc3 : c' = 0 ∨ c' = 1 := by
      have : c' < 2 := hc'; omega
    rcases hc3 with rfl | rfl
    · exact absurd (show CutS VineType.VIII.template 0 (VineType.VIII.template.slots[0]'(by decide)) by
        decide +kernel) hncut
    · refine rung_witness R hc hi1 hi2 ?_
      intro z hz hzr
      have hgd : R.k.getD 1 0 = R.k[1]'hck := by simp [List.getD_eq_getElem?_getD, hck]
      rw [hgd] at hi2
      exact hchain i (by omega) z hz hzr

theorem hlower_VII {G : Garden w} {f : GBranch G.tree → ℕ} {p : ℕ} {Reg : GNode G.tree → Prop}
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : VineRealization G.molecule VineType.VII S a b} (h : PeelCtx G f p Reg VineType.VII S a b R) {q : ℕ}
    (hjoint : ∀ z ∈ S, R.f z < 2 → q ≤ f z)
    (hgood : ∀ z ∈ S, ∀ g, g ∈ (VineType.VII.expand R.k).groups → GoodGroup VineType.VII R.k g →
      R.f z ∈ g → q ≤ f z) : ∀ z ∈ S, q ≤ f z := by
  have hc : 1 < VineType.VII.template.slots.length := by decide
  have hck : 1 < R.k.length := by rw [R.length_eq]; exact hc
  have hs1 : VineType.VII.template.slots[1]'hc = ((5, 7), (6, 8)) := rfl
  have hA : PosA VineType.VII.template (VineType.VII.template.slots[1]'hc) [4, 5, 6] := by
    rw [hs1]; decide +kernel
  have hB : PosB VineType.VII.template 1 (VineType.VII.template.slots[1]'hc) [4, 5, 6] := by
    rw [hs1]; decide +kernel
  have h2 : kap [4, 5, 6] (VineType.VII.template.slots[1]'hc).1.2 = 0 := by rw [hs1]; decide +kernel
  have hxg : ∃ g ∈ VineType.VII.template.groups, (VineType.VII.template.slots[1]'hc).1.1 ∈ g ∧
      (VineType.VII.template.slots[1]'hc).2.1 ∈ g := by
    rw [hs1]; exact ⟨[4, 5, 6], by decide, by decide, by decide⟩
  have hyg : ∃ g ∈ VineType.VII.template.groups, (VineType.VII.template.slots[1]'hc).1.2 ∈ g ∧
      (VineType.VII.template.slots[1]'hc).2.2 ∈ g := by
    rw [hs1]; exact ⟨[7, 8], by decide, by decide, by decide⟩
  have e1e : pos1 VineType.VII R.k 1 hc hck (R.k[1]'hck + 1) = 7 := by
    simp [pos1, railSeq, VineType.template]
  have e2e : pos2 VineType.VII R.k 1 hc hck (R.k[1]'hck + 1) = 8 := by
    simp [pos2, railSeq, VineType.template]
  have hq0 : ∀ z ∈ S, (R.f z = pos1 VineType.VII R.k 1 hc hck (R.k[1]'hck + 1) ∨
      R.f z = pos2 VineType.VII R.k 1 hc hck (R.k[1]'hck + 1)) → q ≤ f z := by
    intro z hz hzr; rw [e1e, e2e] at hzr
    exact good_atom hgood hz (g := [7, 8]) (by decide) (by decide +kernel) (by rcases hzr with e | e <;> simp [e])
  have hchain := pos_chain_bwd h hc hA hB h2 hxg hyg hq0
  have e10 : pos1 VineType.VII R.k 1 hc hck 0 = 5 := by simp [pos1, railSeq, VineType.template]
  have e20 : pos2 VineType.VII R.k 1 hc hck 0 = 6 := by simp [pos2, railSeq, VineType.template]
  have hQ0 : ∀ z ∈ S, (R.f z = 5 ∨ R.f z = 6) → q ≤ f z := by
    intro z hz hzr
    have := hchain (R.k[1]'hck + 1) le_rfl z hz
    rw [Nat.sub_self, e10, e20] at this
    exact this hzr
  refine lower_cover R h.hcoh hjoint hgood ?_ ?_
  · intro g hg hncut
    simp only [VineType.template, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact base_witness R (by decide) (by decide : (5 : ℕ) ∈ [4, 5, 6]) (fun z hz hzv => hQ0 z hz (Or.inl hzv))
    · exact absurd (by decide +kernel) hncut
    · exact absurd (by decide +kernel) hncut
    · exact absurd (by decide +kernel) hncut
  · intro c' hc' hncut i hi1 hi2
    have hc3 : c' = 0 ∨ c' = 1 ∨ c' = 2 := by
      have : c' < 3 := hc'; omega
    rcases hc3 with rfl | rfl | rfl
    · exact absurd (show CutS VineType.VII.template 0 (VineType.VII.template.slots[0]'(by decide)) by
        decide +kernel) hncut
    · refine rung_witness R hc hi1 hi2 ?_
      intro z hz hzr
      have hgd : R.k.getD 1 0 = R.k[1]'hck := by simp [List.getD_eq_getElem?_getD, hck]
      rw [hgd] at hi2
      have := hchain (R.k[1]'hck + 1 - i) (by omega) z hz
      rw [show R.k[1]'hck + 1 - (R.k[1]'hck + 1 - i) = i by omega] at this
      exact this hzr
    · exact absurd (show CutS VineType.VII.template 2 (VineType.VII.template.slots[2]'(by decide)) by
        decide +kernel) hncut

end WaveTurbulence.LayerCnt
