/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.PosChain
import Mathlib.Tactic

/-! # The lower layer bound on the group `H` of vines (V)–(VIII) (TARGET layervine, L1531)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open WaveTurbulence WaveTurbulence.Vine TTree
variable {w : ℕ}

instance (T : VineTemplate) (g : List ℕ) : Decidable (CutG T g) := by
  unfold CutG; dsimp only; infer_instance

instance (T : VineTemplate) (j : ℕ) (s : (ℕ × ℕ) × (ℕ × ℕ)) : Decidable (CutS T j s) := by
  unfold CutS; dsimp only; infer_instance

section helpers
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {X : VineType}
  {S : Finset V} {a b : V}

theorem atom_lt (R : VineRealization M X S a b) {z : V} (hz : z ∈ S) : R.f z < (X.expand R.k).n := by
  have : R.f z ∈ S.image R.f := Finset.mem_image_of_mem _ hz
  rw [R.image_eq] at this; simpa using this

theorem exists_atom (R : VineRealization M X S a b) {v : ℕ} (hv : v < (X.expand R.k).n) :
    ∃ z ∈ S, R.f z = v := by
  have : v ∈ S.image R.f := by rw [R.image_eq]; simpa using hv
  obtain ⟨z, hz, h⟩ := Finset.mem_image.mp this
  exact ⟨z, hz, h⟩

theorem group_of_atom (R : VineRealization M X S a b) {z : V} (hz : z ∈ S) (h2 : 2 ≤ R.f z) :
    ∃ g ∈ (X.expand R.k).groups, R.f z ∈ g := by
  have := (mem_expand_groups_iff X R.k (R.f z)).mpr ⟨h2, atom_lt R hz⟩
  obtain ⟨g, hg, hzg⟩ := List.mem_flatten.mp this
  exact ⟨g, hg, hzg⟩

theorem via_group (R : VineRealization M X S a b) {f : V → ℕ} (hcoh : Coherent f (realizedGroups R))
    {g : List ℕ} (hg : g ∈ (X.expand R.k).groups) {z z' : V} (hz : z ∈ S) (hz' : z' ∈ S)
    (hzg : R.f z ∈ g) (hz'g : R.f z' ∈ g) {q : ℕ} (hq : q ≤ f z') : q ≤ f z := by
  have hgrp : S.toList.filter (fun v => R.f v ∈ g) ∈ realizedGroups R := by
    unfold realizedGroups
    exact List.mem_map.mpr ⟨g, hg, rfl⟩
  have := hcoh _ hgrp z (by simp only [List.mem_filter, Finset.mem_toList, decide_eq_true_eq]; exact ⟨hz, hzg⟩)
    z' (by simp only [List.mem_filter, Finset.mem_toList, decide_eq_true_eq]; exact ⟨hz', hz'g⟩)
  rw [this]; exact hq

end helpers


theorem rung_pos (X : VineType) (ks : List ℕ) {c : ℕ} (hc : c < X.template.slots.length)
    (hck : c < ks.length) {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ ks[c]'hck) {v : ℕ}
    (hv : v ∈ rungGroup X ks c i) : v = pos1 X ks c hc hck i ∨ v = pos2 X ks c hc hck i := by
  have hgd : ks.getD c 0 = ks[c]'hck := by simp [List.getD_eq_getElem?_getD, hck]
  unfold rungGroup at hv
  rw [hgd] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  unfold pos1 pos2 railSeq
  rw [if_neg (by omega), if_pos hi2, if_neg (by omega), if_pos hi2]
  rcases hv with rfl | rfl
  · left; simp
  · right; simp


section cover
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {X : VineType}
  {S : Finset V} {a b : V}

/-- **Cover of all atoms.** Joints, good groups, and one witness atom in each non-good group. -/
theorem lower_cover (R : VineRealization M X S a b) {f : V → ℕ} (hcoh : Coherent f (realizedGroups R))
    {q : ℕ} (hjoint : ∀ z ∈ S, R.f z < 2 → q ≤ f z)
    (hgood : ∀ z ∈ S, ∀ g, g ∈ (X.expand R.k).groups → GoodGroup X R.k g → R.f z ∈ g → q ≤ f z)
    (hHbase : ∀ g ∈ X.template.groups, ¬ CutG X.template g → ∃ z0 ∈ S, R.f z0 ∈ g ∧ q ≤ f z0)
    (hHrung : ∀ c, ∀ hc : c < X.template.slots.length, ¬ CutS X.template c (X.template.slots[c]'hc) →
      ∀ i, 1 ≤ i → i ≤ R.k.getD c 0 → ∃ z0 ∈ S, R.f z0 ∈ rungGroup X R.k c i ∧ q ≤ f z0) :
    ∀ z ∈ S, q ≤ f z := by
  intro z hz
  by_cases h2 : R.f z < 2
  · exact hjoint z hz h2
  obtain ⟨g, hg, hzg⟩ := group_of_atom R hz (by omega)
  rcases expand_groups_cases X R.k R.length_eq hg with hgb | ⟨c, hc, i, hi1, hi2, rfl⟩
  · by_cases hcut : CutG X.template g
    · exact hgood z hz g hg (Or.inl ⟨hgb, hcut⟩) hzg
    · obtain ⟨z0, hz0, hz0g, hz0q⟩ := hHbase g hgb hcut
      exact via_group R hcoh hg hz hz0 hzg hz0g hz0q
  · by_cases hcut : CutS X.template c (X.template.slots[c]'hc)
    · exact hgood z hz _ hg (Or.inr ⟨c, hc, hcut, i, hi1, hi2, rfl⟩) hzg
    · obtain ⟨z0, hz0, hz0g, hz0q⟩ := hHrung c hc hcut i hi1 hi2
      exact via_group R hcoh hg hz hz0 hzg hz0g hz0q

end cover


section witness
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {X : VineType}
  {S : Finset V} {a b : V}

theorem exists_atom_in_group (R : VineRealization M X S a b) {g : List ℕ}
    (hg : g ∈ (X.expand R.k).groups) {v : ℕ} (hv : v ∈ g) : ∃ z ∈ S, R.f z = v := by
  have := (mem_expand_groups_iff X R.k v).mp (List.mem_flatten.mpr ⟨g, hg, hv⟩)
  exact exists_atom R this.2

theorem base_witness (R : VineRealization M X S a b) {f : V → ℕ} {q : ℕ} {g : List ℕ}
    (hg : g ∈ X.template.groups) {v : ℕ} (hv : v ∈ g)
    (hQ : ∀ z ∈ S, R.f z = v → q ≤ f z) : ∃ z0 ∈ S, R.f z0 ∈ g ∧ q ≤ f z0 := by
  obtain ⟨z, hz, hzv⟩ := exists_atom_in_group R (base_group_mem_expand X R.k hg) hv
  exact ⟨z, hz, by rw [hzv]; exact hv, hQ z hz hzv⟩

theorem rung_witness (R : VineRealization M X S a b) {f : V → ℕ} {q : ℕ} {c : ℕ}
    (hc : c < X.template.slots.length) {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ R.k.getD c 0)
    (hQ : ∀ z ∈ S, (R.f z = pos1 X R.k c hc (by rw [R.length_eq]; exact hc) i ∨
      R.f z = pos2 X R.k c hc (by rw [R.length_eq]; exact hc) i) → q ≤ f z) :
    ∃ z0 ∈ S, R.f z0 ∈ rungGroup X R.k c i ∧ q ≤ f z0 := by
  have hck : c < R.k.length := by rw [R.length_eq]; exact hc
  have hmem := rungGroup_mem X R.k R.length_eq c hc i hi1 hi2
  have hv : pos1 X R.k c hc hck i ∈ rungGroup X R.k c i := by
    have hgd : R.k.getD c 0 = R.k[c]'hck := by simp [List.getD_eq_getElem?_getD, hck]
    rw [hgd] at hi2
    unfold rungGroup pos1 railSeq
    rw [if_neg (by omega), if_pos hi2, hgd]
    simp
  obtain ⟨z, hz, hzv⟩ := exists_atom_in_group R hmem hv
  exact ⟨z, hz, by rw [hzv]; exact hv, hQ z hz (Or.inl hzv)⟩

end witness

end WaveTurbulence.LayerCnt
