/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.HLower
import Mathlib.Tactic

/-! # The lower layer bound for vine (V) (TARGET layervine, L1531)

Vine (V) has no cut group: all atoms lie in the group `H`.  The exit lemma is applied to the cut at the joints,
to the rail-position cuts of the ladder (peeling it rung by rung), and to the cut before the last group.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open WaveTurbulence WaveTurbulence.Vine TTree
variable {w : ℕ}

theorem hlower_V {G : Garden w} {f : GBranch G.tree → ℕ} {p : ℕ} {Reg : GNode G.tree → Prop}
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : VineRealization G.molecule VineType.V S a b} (h : PeelCtx G f p Reg VineType.V S a b R) {q : ℕ}
    (hjoint : ∀ z ∈ S, R.f z < 2 → q ≤ f z) : ∀ z ∈ S, q ≤ f z := by
  have hc : 0 < VineType.V.template.slots.length := by decide
  have hck : 0 < R.k.length := by rw [R.length_eq]; exact hc
  -- the cut at the joints
  obtain ⟨KA, hKA, _⟩ := kcut_ext VineType.V R.k R.length_eq (K0 := [2, 3, 4, 5, 6, 7, 8])
    (e1 := (2, 0)) (e2 := (3, 1)) (by decide +kernel)
  have hQA : ∀ z ∈ S, (R.f z = 2 ∨ R.f z = 3) → q ≤ f z :=
    cut_step' h hKA ⟨[2, 3], base_group_mem_expand _ _ (by decide), by simp, by simp⟩
      (fun z hz hzr => hjoint z hz (by simp at hzr; omega))
  -- the ladder
  have hs0 : VineType.V.template.slots[0]'hc = ((2, 4), (3, 5)) := rfl
  have hA : PosA VineType.V.template (VineType.V.template.slots[0]'hc) [4, 5, 6, 7, 8] := by
    rw [hs0]; decide +kernel
  have hB : PosB VineType.V.template 0 (VineType.V.template.slots[0]'hc) [4, 5, 6, 7, 8] := by
    rw [hs0]; decide +kernel
  have h2 : kap [4, 5, 6, 7, 8] (VineType.V.template.slots[0]'hc).1.2 = 2 := by
    rw [hs0]; decide +kernel
  have hxg : ∃ g ∈ VineType.V.template.groups, (VineType.V.template.slots[0]'hc).1.1 ∈ g ∧
      (VineType.V.template.slots[0]'hc).2.1 ∈ g := by
    rw [hs0]; exact ⟨[2, 3], by decide, by decide, by decide⟩
  have hyg : ∃ g ∈ VineType.V.template.groups, (VineType.V.template.slots[0]'hc).1.2 ∈ g ∧
      (VineType.V.template.slots[0]'hc).2.2 ∈ g := by
    rw [hs0]; exact ⟨[4, 5], by decide, by decide, by decide⟩
  have e10 : pos1 VineType.V R.k 0 hc hck 0 = 2 := by simp [pos1, railSeq, VineType.template]
  have e20 : pos2 VineType.V R.k 0 hc hck 0 = 3 := by simp [pos2, railSeq, VineType.template]
  have hq0 : ∀ z ∈ S, (R.f z = pos1 VineType.V R.k 0 hc hck 0 ∨ R.f z = pos2 VineType.V R.k 0 hc hck 0) →
      q ≤ f z := by
    intro z hz hzr; rw [e10, e20] at hzr; exact hQA z hz hzr
  have hchain := pos_chain_fwd h hc hA hB h2 hxg hyg hq0
  have e1e : pos1 VineType.V R.k 0 hc hck (R.k[0]'hck + 1) = 4 := by
    simp [pos1, railSeq, VineType.template]
  have e2e : pos2 VineType.V R.k 0 hc hck (R.k[0]'hck + 1) = 5 := by
    simp [pos2, railSeq, VineType.template]
  have hQD : ∀ z ∈ S, (R.f z = 4 ∨ R.f z = 5) → q ≤ f z := by
    intro z hz hzr
    refine hchain (R.k[0]'hck + 1) le_rfl z hz ?_
    rw [e1e, e2e]; exact hzr
  -- the cut before the last group
  obtain ⟨KC, hKC, _⟩ := kcut_ext VineType.V R.k R.length_eq (K0 := [6, 7, 8])
    (e1 := (6, 4)) (e2 := (7, 5)) (by decide +kernel)
  have hQC : ∀ z ∈ S, (R.f z = 6 ∨ R.f z = 7) → q ≤ f z :=
    cut_step' h hKC ⟨[6, 7, 8], base_group_mem_expand _ _ (by decide), by simp, by simp⟩
      (fun z hz hzr => hQD z hz (by simpa using hzr))
  -- cover
  refine lower_cover R h.hcoh hjoint ?_ ?_ ?_
  · intro z hz g hg hgood
    exfalso
    rcases hgood with ⟨hgb, hcut⟩ | ⟨c', hc', hS, i, _⟩
    · revert hgb hcut
      have : ∀ g ∈ VineType.V.template.groups, ¬ CutG VineType.V.template g := by decide +kernel
      intro hgb hcut; exact this g hgb hcut
    · have hc0 : c' = 0 := by have : c' < 1 := hc'; omega
      subst hc0
      have : ¬ CutS VineType.V.template 0 (VineType.V.template.slots[0]'hc) := by
        rw [hs0]; decide +kernel
      exact this hS
  · intro g hg _
    simp only [VineType.template, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact base_witness R (by decide) (by decide : (6 : ℕ) ∈ [6, 7, 8]) (fun z hz hzv => hQC z hz (Or.inl hzv))
    · exact base_witness R (by decide) (by decide : (2 : ℕ) ∈ [2, 3]) (fun z hz hzv => hQA z hz (Or.inl hzv))
    · exact base_witness R (by decide) (by decide : (4 : ℕ) ∈ [4, 5]) (fun z hz hzv => hQD z hz (Or.inl hzv))
  · intro c' hc' _ i hi1 hi2
    have hc0 : c' = 0 := by have : c' < 1 := hc'; omega
    subst hc0
    refine rung_witness R hc hi1 hi2 ?_
    intro z hz hzr
    have hgd : R.k.getD 0 0 = R.k[0]'hck := by simp [List.getD_eq_getElem?_getD, hck]
    rw [hgd] at hi2
    exact hchain i (by omega) z hz hzr

end WaveTurbulence.LayerCnt
