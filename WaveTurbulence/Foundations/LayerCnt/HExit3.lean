/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.HExit2
import Mathlib.Tactic

/-! # The exit lemma, parent-exit / parent-exit case (TARGET layervine, L1531)

If the two exits of `K` are both parent darts of branching nodes `c₁, c₂`, then `K` is the union of the subtrees
of `c₁, c₂`, whose leaves are completely paired; the canonical criterion for `(c₁, c₂)` is the conclusion.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open TTree
variable {w : ℕ}

/-- The criterion `canonequiv` (ii) for the minimum-parent extension of `f`, restricted to nodes of `Reg`. -/
@[expose] def CanonPairs (G : Garden w) (f : GBranch G.tree → ℕ) (p : ℕ) (Reg : GNode G.tree → Prop) : Prop :=
  ∀ a a' : GNode G.tree, Reg a → Reg a' → a.Incomparable a' →
    G.CompletelyPaired (a.leavesBelow ∪ a'.leavesBelow) →
      min (LFTwist.branchParentValue G f p a) (LFTwist.branchParentValue G f p a') ≤
        max (LFTwist.extendBranchLayers G f p a) (LFTwist.extendBranchLayers G f p a')

theorem upDart_inj {G : Garden w} {c c' : GBranch G.tree} {hc : c.1.2 ≠ []} {hc' : c'.1.2 ≠ []}
    (h : upDart G c hc = upDart G c' hc') : c = c' := by
  have := Sum.inl.inj h
  exact congrArg Subtype.val (Prod.mk.inj this).1

theorem upDart_ne_down {G : Garden w} {c c' : GBranch G.tree} {hc : c.1.2 ≠ []} {hc' : c'.1.2 ≠ []} :
    upDart G c hc ≠ downDart G c' hc' := by
  intro h
  have := (Prod.mk.inj (Sum.inl.inj h)).2
  simp at this

theorem upDart_ne_lp {G : Garden w} {c : GBranch G.tree} {hc : c.1.2 ≠ []} {ℓ : GLeaf G.tree}
    {hm : G.mark ℓ = none} {hr : ℓ.1.2 ≠ []} {hp : (G.pair ℓ).1.2 ≠ []} :
    upDart G c hc ≠ lpDart G ℓ hm hr hp := fun h => Sum.inl_ne_inr h

theorem downDart_ne_lp {G : Garden w} {c : GBranch G.tree} {hc : c.1.2 ≠ []} {ℓ : GLeaf G.tree}
    {hm : G.mark ℓ = none} {hr : ℓ.1.2 ≠ []} {hp : (G.pair ℓ).1.2 ≠ []} :
    downDart G c hc ≠ lpDart G ℓ hm hr hp := fun h => Sum.inl_ne_inr h

namespace ExitData
variable {G : Garden w} {K : Finset (GBranch G.tree)} {d1 d2 : GardenDart G}

/-- If no child dart is an exit, the descendants of an atom of `K` stay in `K`. -/
theorem desc_mem (h : ExitData G K d1 d2) (hno : ∀ c hc, downDart G c hc ≠ d1 ∧ downDart G c hc ≠ d2)
    {c0 : GBranch G.tree} (hc0 : c0 ∈ K) :
    ∀ n, ∀ y : GBranch G.tree, y.1.2.length = n → c0.toNode.IsDesc y.toNode → y ∈ K := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y hn hd
    by_cases hy : y = c0
    · rw [hy]; exact hc0
    · have hne : c0.1.2 ≠ y.1.2 := by
        intro he
        exact hy (Subtype.ext (Prod.ext hd.1.symm he.symm))
      have hyr : y.1.2 ≠ [] := by
        intro h0
        obtain ⟨hj, q, hq⟩ : c0.1.1 = y.1.1 ∧ ∃ q, c0.1.2 ++ q = y.1.2 := hd
        rw [h0] at hq
        exact hne (by simpa using ((List.append_eq_nil_iff.mp hq).1.trans h0.symm))
      have hd' := isDesc_parent_of_ne (a := c0.toNode) (x := y.toNode) hyr hd hne
      have hlen : (GNode.parent y.toNode hyr).1.2.length < n := by
        rw [← hn]
        show y.1.2.dropLast.length < y.1.2.length
        rw [List.length_dropLast]
        have := List.length_pos_of_ne_nil hyr; omega
      have hpK := ih _ hlen _ rfl hd'
      rcases h.child_mem hyr hpK with hyK | h1 | h2
      · exact hyK
      · exact absurd h1 (hno y hyr).1
      · exact absurd h2 (hno y hyr).2

end ExitData

theorem exit_up_up {G : Garden w} {f : GBranch G.tree → ℕ} {p : ℕ} {Reg : GNode G.tree → Prop}
    (hC : CanonPairs G f p Reg) {K : Finset (GBranch G.tree)} {c1 c2 : GBranch G.tree}
    (hc1 : c1.1.2 ≠ []) (hc2 : c2.1.2 ≠ [])
    (h : ExitData G K (upDart G c1 hc1) (upDart G c2 hc2)) (h12 : upDart G c1 hc1 ≠ upDart G c2 hc2)
    (hc1K : c1 ∈ K) (hc2K : c2 ∈ K) (hp1 : GNode.parent c1.toNode hc1 ∉ K)
    (hp2 : GNode.parent c2.toNode hc2 ∉ K) (hR1 : Reg c1.toNode) (hR2 : Reg c2.toNode) :
    min (f (GNode.parent c1.toNode hc1)) (f (GNode.parent c2.toNode hc2)) ≤
      max (f c1) (f c2) := by
  have hno : ∀ c hc, downDart G c hc ≠ upDart G c1 hc1 ∧ downDart G c hc ≠ upDart G c2 hc2 :=
    fun c hc => ⟨fun e => upDart_ne_down e.symm, fun e => upDart_ne_down e.symm⟩
  have hs1 := h.desc_mem hno hc1K
  have hs2 := h.desc_mem hno hc2K
  have hcover : ∀ x ∈ K, c1.toNode.IsDesc x.toNode ∨ c2.toNode.IsDesc x.toNode := by
    intro x hx
    obtain ⟨c, hc, hcd, hdesc⟩ := h.exit_tops x hx
    rcases hcd with e | e
    · rw [upDart_inj e] at hdesc; exact Or.inl hdesc
    · rw [upDart_inj e] at hdesc; exact Or.inr hdesc
  have hne12 : c1 ≠ c2 := fun e => h12 (by subst e; rfl)
  have hinc : c1.toNode.Incomparable c2.toNode := by
    constructor
    · intro hd
      have hn : c1.1.2 ≠ c2.1.2 := fun he => hne12 (Subtype.ext (Prod.ext hd.1 he))
      exact hp2 (hs1 _ _ rfl (isDesc_parent_of_ne hc2 hd hn))
    · intro hd
      have hn : c2.1.2 ≠ c1.1.2 := fun he => hne12 (Subtype.ext (Prod.ext hd.1.symm he.symm))
      exact hp1 (hs2 _ _ rfl (isDesc_parent_of_ne hc1 hd hn))
  have hcp : G.CompletelyPaired (c1.toNode.leavesBelow ∪ c2.toNode.leavesBelow) := by
    intro ℓ hℓ
    have hL : ∃ c : GBranch G.tree, (c = c1 ∨ c = c2) ∧ c.toNode.IsDesc ℓ.toNode ∧ c.1.2 ≠ [] := by
      rcases Finset.mem_union.mp hℓ with hl | hl
      · exact ⟨c1, Or.inl rfl, (Finset.mem_filter.mp hl).2, hc1⟩
      · exact ⟨c2, Or.inr rfl, (Finset.mem_filter.mp hl).2, hc2⟩
    obtain ⟨c, hcc, hdesc, hcr⟩ := hL
    have hr : ℓ.1.2 ≠ [] := by
      intro h0
      obtain ⟨hj, q, hq⟩ : c.1.1 = ℓ.1.1 ∧ ∃ q, c.1.2 ++ q = ℓ.1.2 := hdesc
      rw [h0] at hq
      exact hcr (List.append_eq_nil_iff.mp hq).1
    have hsc : ∀ y : GBranch G.tree, c.toNode.IsDesc y.toNode → y ∈ K := by
      rcases hcc with rfl | rfl
      · exact fun y hy => hs1 _ _ rfl hy
      · exact fun y hy => hs2 _ _ rfl hy
    have hpK : GNode.parent ℓ.toNode hr ∈ K :=
      hsc _ ((branch_isDesc_leaf_iff c ℓ hr).mp hdesc)
    obtain ⟨hm, hp⟩ := leaf_valid_of_deg4 ℓ hr (h.deg4 _ hpK)
    refine ⟨Garden.pair_ne_of_unmarked hm, ?_⟩
    by_cases hq : GNode.parent (G.pair ℓ).toNode hp ∈ K
    · rcases hcover _ hq with hd | hd
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (branch_isDesc_leaf_iff c1 _ hp).mpr hd⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (branch_isDesc_leaf_iff c2 _ hp).mpr hd⟩)
    · exfalso
      rcases h.ex (lpDart G ℓ hm hr hp) hpK hq with e | e
      · exact upDart_ne_lp e.symm
      · exact upDart_ne_lp e.symm
  have := hC _ _ hR1 hR2 hinc hcp
  rw [pv_nonroot f p hc1, pv_nonroot f p hc2, LFTwist.extendBranchLayers_branch,
    LFTwist.extendBranchLayers_branch] at this
  exact this

end WaveTurbulence.LayerCnt
