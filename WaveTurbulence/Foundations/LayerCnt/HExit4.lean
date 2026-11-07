/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.HExit3
import Mathlib.Tactic

/-! # The exit lemma (TARGET layervine, L1531; proof of the claim for the group `H`)

For a set `K` of degree-four atoms whose only exit darts are `d₁ ≠ d₂` with `f (atom d₁) = f (atom d₂)`, and for
the minimum-parent extension of `f` satisfying the canonical pair criterion on the nodes of the region,
`min (f (atom (mate d₁)), f (atom (mate d₂))) ≤ f (atom d₁)`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open TTree
variable {w : ℕ}

theorem exit_up_lp {G : Garden w} {f : GBranch G.tree → ℕ} {p : ℕ} {Reg : GNode G.tree → Prop}
    (hC : CanonPairs G f p Reg) {K : Finset (GBranch G.tree)} {c1 : GBranch G.tree}
    (hc1 : c1.1.2 ≠ []) {ℓ0 : GLeaf G.tree} (hm : G.mark ℓ0 = none) (hr : ℓ0.1.2 ≠ [])
    (hp : (G.pair ℓ0).1.2 ≠ [])
    (h : ExitData G K (upDart G c1 hc1) (lpDart G ℓ0 hm hr hp))
    (hc1K : c1 ∈ K) (hz4 : GNode.parent ℓ0.toNode hr ∈ K)
    (hz3 : GNode.parent (G.pair ℓ0).toNode hp ∉ K) (hR1 : Reg c1.toNode)
    (hR' : Reg (G.pair ℓ0).toNode) (hco : f c1 = f (GNode.parent ℓ0.toNode hr)) :
    min (f (GNode.parent c1.toNode hc1)) (f (GNode.parent (G.pair ℓ0).toNode hp)) ≤ f c1 := by
  have hno : ∀ c hc, downDart G c hc ≠ upDart G c1 hc1 ∧ downDart G c hc ≠ lpDart G ℓ0 hm hr hp :=
    fun c hc => ⟨fun e => upDart_ne_down e.symm, fun e => downDart_ne_lp e⟩
  have hs1 := h.desc_mem hno hc1K
  have hcover : ∀ x ∈ K, c1.toNode.IsDesc x.toNode := by
    intro x hx
    obtain ⟨c, hc, hcd, hdesc⟩ := h.exit_tops x hx
    rcases hcd with e | e
    · rw [upDart_inj e] at hdesc; exact hdesc
    · exact absurd e upDart_ne_lp
  have hinc : c1.toNode.Incomparable (G.pair ℓ0).toNode := by
    constructor
    · intro hd
      exact hz3 (hs1 _ _ rfl ((branch_isDesc_leaf_iff c1 _ hp).mp hd))
    · intro hd
      exact leaf_not_isDesc_branch (G.pair ℓ0) _ c1 rfl hd
  have hcp : G.CompletelyPaired (c1.toNode.leavesBelow ∪ (G.pair ℓ0).toNode.leavesBelow) := by
    intro ℓ hℓ
    rcases Finset.mem_union.mp hℓ with hl | hl
    · have hdesc := (Finset.mem_filter.mp hl).2
      have hr' : ℓ.1.2 ≠ [] := by
        intro h0
        obtain ⟨hj, q, hq⟩ : c1.1.1 = ℓ.1.1 ∧ ∃ q, c1.1.2 ++ q = ℓ.1.2 := hdesc
        rw [h0] at hq
        exact hc1 (List.append_eq_nil_iff.mp hq).1
      have hpK : GNode.parent ℓ.toNode hr' ∈ K := hs1 _ _ rfl ((branch_isDesc_leaf_iff c1 ℓ hr').mp hdesc)
      obtain ⟨hm', hp'⟩ := leaf_valid_of_deg4 ℓ hr' (h.deg4 _ hpK)
      refine ⟨Garden.pair_ne_of_unmarked hm', ?_⟩
      by_cases hq : GNode.parent (G.pair ℓ).toNode hp' ∈ K
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (branch_isDesc_leaf_iff c1 _ hp').mpr (hcover _ hq)⟩)
      · rcases h.ex (lpDart G ℓ hm' hr' hp') hpK hq with e | e
        · exact absurd e.symm upDart_ne_lp
        · have hℓ : ℓ = ℓ0 := congrArg Subtype.val (Sum.inr.inj e)
          subst hℓ
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, GNode.isDesc_refl _⟩)
    · have hdesc := (Finset.mem_filter.mp hl).2
      have heq : G.pair ℓ0 = ℓ := GLeaf.eq_of_isDesc hdesc
      subst heq
      rw [G.pair_pair]
      refine ⟨fun e => Garden.pair_ne_of_unmarked hm (e.symm), ?_⟩
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (branch_isDesc_leaf_iff c1 _ hr).mpr (hcover _ hz4)⟩)
  have := hC _ _ hR1 hR' hinc hcp
  rw [pv_nonroot f p hc1, pv_nonroot f p hp, LFTwist.extendBranchLayers_branch,
    LFTwist.extendBranchLayers_leaf, pv_nonroot f p hp, G.pair_pair, pv_nonroot f p hr] at this
  rw [← hco] at this
  have hmin : min (f (GNode.parent (G.pair ℓ0).toNode hp)) (f c1) ≤ f c1 := min_le_right _ _
  have : max (f c1) (min (f (GNode.parent (G.pair ℓ0).toNode hp)) (f c1)) = f c1 := max_eq_left hmin
  omega

end WaveTurbulence.LayerCnt
