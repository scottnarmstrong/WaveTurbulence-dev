/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.HChain
public import WaveTurbulence.Foundations.LayerCnt.VineGroups
public import WaveTurbulence.Foundations.LayerCnt.GoodGroups
import Mathlib.Tactic

/-! # Peeling an inserted ladder rung by rung (TARGET layervine, L1531)

Positions `0, …, k + 1` of an inserted ladder at slot `c`: position `0` is the entry end `(x, x')`, position `m` the
`m`-th rung `(u_m, v_m)` and position `k + 1` the exit end `(y, y')`.  A lower bound on the layers at one position
propagates to the next one through the rail-position cut (`cut_step`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open WaveTurbulence WaveTurbulence.Vine TTree
variable {w : ℕ}

theorem rungGroup_mem (X : VineType) (ks : List ℕ) (hk : ks.length = X.template.slots.length)
    (c : ℕ) (hc : c < X.template.slots.length) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ ks.getD c 0) :
    rungGroup X ks c i ∈ (X.expand ks).groups := by
  have hck : c < ks.length := by omega
  have hgd : ks.getD c 0 = ks[c] := by simp [List.getD_eq_getElem?_getD, hck]
  rw [hgd] at hi2
  set xs := X.template.slots.zip ks with hxs
  have hcl : c < xs.length := by simp [hxs, List.length_zip, hk, hc]
  have hloc : xs = xs.take c ++ (xs[c]'hcl) :: xs.drop (c + 1) := by
    rw [← List.drop_eq_getElem_cons hcl, List.take_append_drop]
  have hxc : xs[c]'hcl = (X.template.slots[c]'hc, ks[c]) := by simp [hxs, List.getElem_zip]
  have hexp : X.expand ks = (xs.drop (c + 1)).foldl (fun U sk => insertRungs U sk.1 sk.2)
      (insertRungs ((xs.take c).foldl (fun U sk => insertRungs U sk.1 sk.2) X.template)
        (X.template.slots[c]'hc) ks[c]) := by
    unfold VineType.expand
    change xs.foldl _ X.template = _
    conv_lhs => rw [hloc]
    rw [List.foldl_append, List.foldl_cons, hxc]
  rw [hexp]
  apply fold_groups_mem
  have hn : ((xs.take c).foldl (fun U sk => insertRungs U sk.1 sk.2) X.template).n =
      X.template.n + 2 * (ks.take c).sum := by
    rw [fold_insertRungs_atoms]
    have : (xs.take c).map Prod.snd = ks.take c := by
      rw [List.map_take, hxs, List.map_snd_zip (by omega)]
    rw [this]
  have := rung_group_mem ((xs.take c).foldl (fun U sk => insertRungs U sk.1 sk.2) X.template)
    (X.template.slots[c]'hc) (k := ks[c]) hi1 hi2
  rw [hn] at this
  unfold rungGroup
  rw [hgd]
  convert this using 2


/-- The context of a peeling argument. -/
structure PeelCtx {w : ℕ} (G : Garden w) (f : GBranch G.tree → ℕ) (p : ℕ) (Reg : GNode G.tree → Prop)
    (X : VineType) (S : Finset (GBranch G.tree)) (a b : GBranch G.tree)
    (R : VineRealization G.molecule X S a b) : Prop where
  hf : LFTwist.IsBranchPrelayering G f
  hC : CanonPairs G f p Reg
  hB : G.molecule.DegreeBlock S a b
  hRegS : ∀ x ∈ S, x ≠ a → Reg x.toNode
  hRegLeaf : ∀ ℓ : GLeaf G.tree, ∀ hr : ℓ.1.2 ≠ [], GNode.parent ℓ.toNode hr ∈ S →
    GNode.parent ℓ.toNode hr ≠ a → Reg (G.pair ℓ).toNode
  hcoh : Coherent f (realizedGroups R)

theorem cut_step' {G : Garden w} {f : GBranch G.tree → ℕ} {p : ℕ} {Reg : GNode G.tree → Prop}
    {X : VineType} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : VineRealization G.molecule X S a b} (h : PeelCtx G f p Reg X S a b R)
    {K : ℕ → Prop} {e1 e2 : ℕ × ℕ} (hK : IsKCut (X.expand R.k) K e1 e2)
    (hg : ∃ g ∈ (X.expand R.k).groups, e1.1 ∈ g ∧ e2.1 ∈ g) {q : ℕ}
    (hbelow : ∀ z ∈ S, (R.f z = e1.2 ∨ R.f z = e2.2) → q ≤ f z) :
    ∀ z ∈ S, (R.f z = e1.1 ∨ R.f z = e2.1) → q ≤ f z :=
  cut_step h.hf h.hC h.hB R h.hRegS h.hRegLeaf h.hcoh hK hg hbelow

/-- The `m`-th atoms of the two rails of the ladder at slot `c`. -/
@[expose] def pos1 (X : VineType) (ks : List ℕ) (c : ℕ) (hc : c < X.template.slots.length)
    (hck : c < ks.length) (m : ℕ) : ℕ :=
  railSeq (X.template.slots[c]'hc).1.1 (X.template.slots[c]'hc).1.2 (ks[c]'hck)
    (fun i => X.template.n + 2 * (ks.take c).sum + i) m

@[expose] def pos2 (X : VineType) (ks : List ℕ) (c : ℕ) (hc : c < X.template.slots.length)
    (hck : c < ks.length) (m : ℕ) : ℕ :=
  railSeq (X.template.slots[c]'hc).2.1 (X.template.slots[c]'hc).2.2 (ks[c]'hck)
    (fun i => X.template.n + 2 * (ks.take c).sum + ks[c]'hck + i) m

section step
variable {G : Garden w} {f : GBranch G.tree → ℕ} {p : ℕ} {Reg : GNode G.tree → Prop}
    {X : VineType} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : VineRealization G.molecule X S a b}

theorem pos_step_fwd (h : PeelCtx G f p Reg X S a b R) {c : ℕ} (hc : c < X.template.slots.length)
    {K0 : List ℕ} (hA : PosA X.template (X.template.slots[c]'hc) K0)
    (hB : PosB X.template c (X.template.slots[c]'hc) K0)
    (h2 : kap K0 (X.template.slots[c]'hc).1.2 = 2) {q j : ℕ}
    (hj : j ≤ R.k[c]'(by rw [R.length_eq]; exact hc))
    (hgrp : ∃ g ∈ (X.expand R.k).groups, pos1 X R.k c hc (by rw [R.length_eq]; exact hc) (j + 1) ∈ g ∧
      pos2 X R.k c hc (by rw [R.length_eq]; exact hc) (j + 1) ∈ g)
    (hq : ∀ z ∈ S, (R.f z = pos1 X R.k c hc (by rw [R.length_eq]; exact hc) j ∨
      R.f z = pos2 X R.k c hc (by rw [R.length_eq]; exact hc) j) → q ≤ f z) :
    ∀ z ∈ S, (R.f z = pos1 X R.k c hc (by rw [R.length_eq]; exact hc) (j + 1) ∨
      R.f z = pos2 X R.k c hc (by rw [R.length_eq]; exact hc) (j + 1)) → q ≤ f z := by
  obtain ⟨K, hK, _, _⟩ := expand_kcutPos X R.k R.length_eq c hc hA hB j hj
  unfold orientE at hK
  rw [if_pos h2, if_pos h2] at hK
  exact cut_step' h hK hgrp hq

theorem pos_step_bwd (h : PeelCtx G f p Reg X S a b R) {c : ℕ} (hc : c < X.template.slots.length)
    {K0 : List ℕ} (hA : PosA X.template (X.template.slots[c]'hc) K0)
    (hB : PosB X.template c (X.template.slots[c]'hc) K0)
    (h2 : kap K0 (X.template.slots[c]'hc).1.2 = 0) {q j : ℕ}
    (hj : j ≤ R.k[c]'(by rw [R.length_eq]; exact hc))
    (hgrp : ∃ g ∈ (X.expand R.k).groups, pos1 X R.k c hc (by rw [R.length_eq]; exact hc) j ∈ g ∧
      pos2 X R.k c hc (by rw [R.length_eq]; exact hc) j ∈ g)
    (hq : ∀ z ∈ S, (R.f z = pos1 X R.k c hc (by rw [R.length_eq]; exact hc) (j + 1) ∨
      R.f z = pos2 X R.k c hc (by rw [R.length_eq]; exact hc) (j + 1)) → q ≤ f z) :
    ∀ z ∈ S, (R.f z = pos1 X R.k c hc (by rw [R.length_eq]; exact hc) j ∨
      R.f z = pos2 X R.k c hc (by rw [R.length_eq]; exact hc) j) → q ≤ f z := by
  obtain ⟨K, hK, _, _⟩ := expand_kcutPos X R.k R.length_eq c hc hA hB j hj
  unfold orientE at hK
  rw [if_neg (by omega), if_neg (by omega)] at hK
  exact cut_step' h hK hgrp hq

end step


theorem base_group_mem_expand (X : VineType) (ks : List ℕ) {g : List ℕ} (hg : g ∈ X.template.groups) :
    g ∈ (X.expand ks).groups := fold_groups_mem _ _ hg

theorem pos_groups (X : VineType) (ks : List ℕ) (hk : ks.length = X.template.slots.length) {c : ℕ}
    (hc : c < X.template.slots.length)
    (hxg : ∃ g ∈ X.template.groups, (X.template.slots[c]'hc).1.1 ∈ g ∧ (X.template.slots[c]'hc).2.1 ∈ g)
    (hyg : ∃ g ∈ X.template.groups, (X.template.slots[c]'hc).1.2 ∈ g ∧ (X.template.slots[c]'hc).2.2 ∈ g)
    {m : ℕ} (hm : m ≤ ks[c]'(by omega) + 1) :
    ∃ g ∈ (X.expand ks).groups, pos1 X ks c hc (by omega) m ∈ g ∧ pos2 X ks c hc (by omega) m ∈ g := by
  have hck : c < ks.length := by omega
  by_cases h0 : m = 0
  · subst h0
    obtain ⟨g, hg, h1, h2⟩ := hxg
    refine ⟨g, base_group_mem_expand X ks hg, ?_, ?_⟩
    · simp [pos1, railSeq, h1]
    · simp [pos2, railSeq, h2]
  · by_cases h1 : m ≤ ks[c]'hck
    · have hmem := rungGroup_mem X ks hk c hc m (by omega) (by simp [List.getD_eq_getElem?_getD, hck]; omega)
      refine ⟨_, hmem, ?_, ?_⟩
      · unfold rungGroup pos1 railSeq
        rw [if_neg h0, if_pos h1]
        simp
      · unfold rungGroup pos2 railSeq
        rw [if_neg h0, if_pos h1]
        simp [List.getD_eq_getElem?_getD, hck]
    · have hm' : m = ks[c]'hck + 1 := by omega
      obtain ⟨g, hg, h1', h2⟩ := hyg
      refine ⟨g, base_group_mem_expand X ks hg, ?_, ?_⟩
      · simp only [pos1, railSeq]; rw [if_neg h0, if_neg h1]; exact h1'
      · simp only [pos2, railSeq]; rw [if_neg h0, if_neg h1]; exact h2

section chain
variable {G : Garden w} {f : GBranch G.tree → ℕ} {p : ℕ} {Reg : GNode G.tree → Prop}
    {X : VineType} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : VineRealization G.molecule X S a b}

theorem pos_chain_fwd (h : PeelCtx G f p Reg X S a b R) {c : ℕ} (hc : c < X.template.slots.length)
    {K0 : List ℕ} (hA : PosA X.template (X.template.slots[c]'hc) K0)
    (hB : PosB X.template c (X.template.slots[c]'hc) K0)
    (h2 : kap K0 (X.template.slots[c]'hc).1.2 = 2)
    (hxg : ∃ g ∈ X.template.groups, (X.template.slots[c]'hc).1.1 ∈ g ∧ (X.template.slots[c]'hc).2.1 ∈ g)
    (hyg : ∃ g ∈ X.template.groups, (X.template.slots[c]'hc).1.2 ∈ g ∧ (X.template.slots[c]'hc).2.2 ∈ g)
    {q : ℕ}
    (hq0 : ∀ z ∈ S, (R.f z = pos1 X R.k c hc (by rw [R.length_eq]; exact hc) 0 ∨
      R.f z = pos2 X R.k c hc (by rw [R.length_eq]; exact hc) 0) → q ≤ f z) :
    ∀ m, m ≤ R.k[c]'(by rw [R.length_eq]; exact hc) + 1 → ∀ z ∈ S,
      (R.f z = pos1 X R.k c hc (by rw [R.length_eq]; exact hc) m ∨
        R.f z = pos2 X R.k c hc (by rw [R.length_eq]; exact hc) m) → q ≤ f z := by
  intro m
  induction m with
  | zero => intro _; exact hq0
  | succ m ih =>
    intro hm
    exact pos_step_fwd h hc hA hB h2 (by omega) (pos_groups X R.k R.length_eq hc hxg hyg (by omega))
      (ih (by omega))

theorem pos_chain_bwd (h : PeelCtx G f p Reg X S a b R) {c : ℕ} (hc : c < X.template.slots.length)
    {K0 : List ℕ} (hA : PosA X.template (X.template.slots[c]'hc) K0)
    (hB : PosB X.template c (X.template.slots[c]'hc) K0)
    (h2 : kap K0 (X.template.slots[c]'hc).1.2 = 0)
    (hxg : ∃ g ∈ X.template.groups, (X.template.slots[c]'hc).1.1 ∈ g ∧ (X.template.slots[c]'hc).2.1 ∈ g)
    (hyg : ∃ g ∈ X.template.groups, (X.template.slots[c]'hc).1.2 ∈ g ∧ (X.template.slots[c]'hc).2.2 ∈ g)
    {q : ℕ}
    (hq0 : ∀ z ∈ S, (R.f z = pos1 X R.k c hc (by rw [R.length_eq]; exact hc)
        (R.k[c]'(by rw [R.length_eq]; exact hc) + 1) ∨
      R.f z = pos2 X R.k c hc (by rw [R.length_eq]; exact hc)
        (R.k[c]'(by rw [R.length_eq]; exact hc) + 1)) → q ≤ f z) :
    ∀ d, d ≤ R.k[c]'(by rw [R.length_eq]; exact hc) + 1 → ∀ z ∈ S,
      (R.f z = pos1 X R.k c hc (by rw [R.length_eq]; exact hc) (R.k[c]'(by rw [R.length_eq]; exact hc) + 1 - d) ∨
        R.f z = pos2 X R.k c hc (by rw [R.length_eq]; exact hc) (R.k[c]'(by rw [R.length_eq]; exact hc) + 1 - d)) →
      q ≤ f z := by
  intro d
  induction d with
  | zero => intro _; simpa using hq0
  | succ d ih =>
    intro hd
    have hj : R.k[c]'(by rw [R.length_eq]; exact hc) + 1 - (d + 1) + 1 =
        R.k[c]'(by rw [R.length_eq]; exact hc) + 1 - d := by omega
    have := pos_step_bwd h hc hA hB h2 (j := R.k[c]'(by rw [R.length_eq]; exact hc) + 1 - (d + 1))
      (by omega) (pos_groups X R.k R.length_eq hc hxg hyg (by omega))
      (by rw [hj]; exact ih (by omega))
    exact this

end chain

end WaveTurbulence.LayerCnt
