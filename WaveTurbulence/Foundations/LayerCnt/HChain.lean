/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.ExitKCut
public import WaveTurbulence.Foundations.LayerCnt.HExit5
public import WaveTurbulence.Foundations.LayerCnt.PosMain
public import WaveTurbulence.Foundations.LayerCnt.KCutExt
public import WaveTurbulence.Foundations.LayerCnt.ChainLower
import Mathlib.Tactic

/-! # One peeling step of the group `H` (TARGET layervine, L1531)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open WaveTurbulence WaveTurbulence.Vine TTree
variable {w : ℕ}

theorem cut_step {G : Garden w} {f : GBranch G.tree → ℕ} (hf : LFTwist.IsBranchPrelayering G f)
    {p : ℕ} {Reg : GNode G.tree → Prop} (hC : CanonPairs G f p Reg) {X : VineType}
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (hB : G.molecule.DegreeBlock S a b)
    (R : VineRealization G.molecule X S a b) (hRegS : ∀ x ∈ S, x ≠ a → Reg x.toNode)
    (hRegLeaf : ∀ ℓ : GLeaf G.tree, ∀ hr : ℓ.1.2 ≠ [], GNode.parent ℓ.toNode hr ∈ S →
      GNode.parent ℓ.toNode hr ≠ a → Reg (G.pair ℓ).toNode)
    (hcoh : Coherent f (realizedGroups R)) {K : ℕ → Prop} {e1 e2 : ℕ × ℕ}
    (hK : IsKCut (X.expand R.k) K e1 e2)
    (hg : ∃ g ∈ (X.expand R.k).groups, e1.1 ∈ g ∧ e2.1 ∈ g) {q : ℕ}
    (hbelow : ∀ z ∈ S, (R.f z = e1.2 ∨ R.f z = e2.2) → q ≤ f z) :
    ∀ z ∈ S, (R.f z = e1.1 ∨ R.f z = e2.1) → q ≤ f z := by
  classical
  obtain ⟨d1, d2, hex, hne, h1in, h1out, h2in, h2out, ha1, hb1, ha2, hb2, hSn⟩ := exit_of_kcut G hB R hK
  have hS1 : G.molecule.atom d1 ∈ S := (Finset.mem_filter.mp h1in).1
  have hS2 : G.molecule.atom d2 ∈ S := (Finset.mem_filter.mp h2in).1
  have hS1' := hSn d1 h1in
  have hS2' := hSn d2 h2in
  obtain ⟨g, hgm, hg1, hg2⟩ := hg
  have hgrp : S.toList.filter (fun v => R.f v ∈ g) ∈ realizedGroups R := by
    unfold realizedGroups
    exact List.mem_map.mpr ⟨g, hgm, rfl⟩
  have hco : f (G.molecule.atom d1) = f (G.molecule.atom d2) := by
    apply hcoh _ hgrp
    · simp only [List.mem_filter, Finset.mem_toList, decide_eq_true_eq]
      exact ⟨hS1, by rw [ha1]; exact hg1⟩
    · simp only [List.mem_filter, Finset.mem_toList, decide_eq_true_eq]
      exact ⟨hS2, by rw [ha2]; exact hg2⟩
  have hKa : ∀ x ∈ S.filter (fun z => K (R.f z)), x ∈ S ∧ x ≠ a := by
    intro x hx
    obtain ⟨hxS, hxK⟩ := Finset.mem_filter.mp hx
    refine ⟨hxS, ?_⟩
    rintro rfl
    have h2 := hK.2.2.2.2.2.2.2.2 _ hxK
    have hj : R.f x ∈ ({R.f x, R.f b} : Finset ℕ) := by simp
    rw [R.joints_eq] at hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    omega
  have hl := exit_lemma hf hC (Finset.filter_subset _ _) hex hne h1in h1out h2in h2out hco hSn
    (fun x hx => hRegS x (hKa x hx).1 (hKa x hx).2)
    (fun ℓ hr hpK => hRegLeaf ℓ hr (hKa _ hpK).1 (hKa _ hpK).2)
  have hq1 : q ≤ f (G.molecule.atom (G.molecule.mate d1)) := hbelow _ hS1' (Or.inl hb1)
  have hq2 : q ≤ f (G.molecule.atom (G.molecule.mate d2)) := hbelow _ hS2' (Or.inr hb2)
  have hqq : q ≤ f (G.molecule.atom d1) := le_trans (le_min hq1 hq2) hl
  intro z hz hzr
  rcases hzr with h | h
  · have : z = G.molecule.atom d1 := R.injOn hz hS1 (h.trans ha1.symm)
    rw [this]; exact hqq
  · have : z = G.molecule.atom d2 := R.injOn hz hS2 (h.trans ha2.symm)
    rw [this]; rw [← hco]; exact hqq

end WaveTurbulence.LayerCnt
