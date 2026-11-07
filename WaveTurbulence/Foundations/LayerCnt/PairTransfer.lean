/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.PosTransfer
import Mathlib.Tactic

/-! # Complete pairing transfers from the skeleton to the decoded garden

If the leaves below two skeleton nodes `a, a'` are completely paired in `S`, and the regular trees at `a, a'` are nil,
then the leaves below the decoded nodes of `a, a'` are completely paired in any decoded garden `G`.
Every pair of `G` is an attachment pair: a couple pair (endpoints under the two roots of its source leaf pair) or a
chain pair (endpoints under the chain's position and off the hole).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open TTree Reg Reg.Skeleton Links LFTwist Twist
variable {w : ℕ} {S G : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS G)

theorem secondLeaf_eq_pair (p : SourcePair S) : p.secondLeaf hS = S.pair (p.firstLeaf hS) := by
  have h1 := pairOfLeaf_sides_pos S hS (p.firstLeaf hS) (sourcePair_first_sign S hS p)
  rw [pairOfLeaf_firstLeaf] at h1
  exact h1.2

theorem firstLeaf_eq_pair (p : SourcePair S) : p.firstLeaf hS = S.pair (p.secondLeaf hS) := by
  rw [secondLeaf_eq_pair hS p, S.pair_pair]

theorem endpoint_partner (q : Pair w) (hq : q ∈ sourcePairs G) (x : GLeaf G.tree) :
    (x.1 = q.1 → (G.pair x).1 = q.2) ∧ (x.1 = q.2 → (G.pair x).1 = q.1) := by
  obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hq
  constructor
  · intro h
    have : x = m := Subtype.ext h
    subst this
    rfl
  · intro h
    have : x = G.pair m := Subtype.ext h
    subst this
    rw [G.pair_pair]

theorem leaf_below_node_eq (ℓ : GLeaf S.tree) (c : GNode S.tree) (h : Below ℓ.1 c.1) : c = ℓ.toNode := by
  obtain ⟨q, rfl⟩ := (nodePieceEquiv S.tree).surjective c
  cases q with
  | inl b => exact (leaf_not_above_branch S.tree ℓ b h).elim
  | inr m =>
    have : ℓ = m := (leaf_desc_iff (G := S) ℓ m).mp ⟨h.1.symm, h.2⟩
    subst this
    rfl

theorem leaf_mem_below_of_under (c : GNode S.tree) (ℓ : GLeaf S.tree) (x : Address w)
    (hc : Below (inflatedPosition S D.tree c) x) (hl : Under (inflatedPosition S D.tree ℓ.toNode) x) :
    ℓ ∈ c.leavesBelow := by
  rw [leafBelow_iff_below]
  have hcmp : Below (inflatedPosition S D.tree c) (inflatedPosition S D.tree ℓ.toNode) ∨
      Below (inflatedPosition S D.tree ℓ.toNode) (inflatedPosition S D.tree c) := by
    have := List.prefix_or_prefix_of_prefix hc.2 hl.2
    rcases this with h | h
    · exact Or.inl ⟨hl.1.trans hc.1, h⟩
    · exact Or.inr ⟨hc.1.symm.trans hl.1.symm, h⟩
  rcases hcmp with h | h
  · exact below_of_pos_below D.tree c ℓ.toNode h
  · have h2 := below_of_pos_below D.tree ℓ.toNode c h
    have := leaf_below_node_eq ℓ c h2
    rw [this]
    exact ⟨rfl, List.prefix_refl _⟩

include hd in
theorem partner_below (c c' : GNode S.tree)
    (hc : ∀ b : GBranch S.tree, b.toNode = c → D.tree b = .nil)
    (hcp : S.CompletelyPaired (c.leavesBelow ∪ c'.leavesBelow)) (x : GLeaf G.tree)
    (hx : Below (inflatedPosition S D.tree c) x.1) :
    Below (inflatedPosition S D.tree c) (G.pair x).1 ∨ Below (inflatedPosition S D.tree c') (G.pair x).1 := by
  have ht : D.forest hS = G.tree := congrArg Raw.tree hd.2
  let x' : GLeaf (D.forest hS) := ⟨x.1, by rw [ht]; exact x.2⟩
  obtain ⟨q, hq, hxq⟩ := (mem_pairEndpoints_iff _ _).mp (D.forest_pairList_cover hS x')
  have hxq' : x.1 = q.1 ∨ x.1 = q.2 := hxq
  have hyq : (G.pair x).1 = q.1 ∨ (G.pair x).1 = q.2 := by
    rcases D.pairList_mem_cases hS q hq with ⟨p, hp⟩ | ⟨b, hb⟩
    · have hqs := D.couple_pair_mem hS hd p q hp
      rcases hxq' with h | h
      · exact Or.inr ((endpoint_partner q hqs x).1 h)
      · exact Or.inl ((endpoint_partner q hqs x).2 h)
    · have hqs := D.chain_pair_mem hS hd b q hb
      rcases hxq' with h | h
      · exact Or.inr ((endpoint_partner q hqs x).1 h)
      · exact Or.inl ((endpoint_partner q hqs x).2 h)
  rcases D.pairList_mem_cases hS q hq with ⟨p, hp⟩ | ⟨b, hb⟩
  · -- couple attachment
    have hend : ∀ z, z = q.1 ∨ z = q.2 →
        Under (inflatedPosition S D.tree (p.firstLeaf hS).toNode) z ∨
        Under (inflatedPosition S D.tree (p.secondLeaf hS).toNode) z := fun z hz =>
      cpl_endpoints_under (D.couple p) _ _ z (Finset.mem_union_right _
        ((mem_pairEndpoints_iff _ _).mpr ⟨q, hp, hz⟩))
    have hxe := hend _ hxq'
    have hye := hend _ hyq
    have reach : ∀ ℓ : GLeaf S.tree, ℓ ∈ c.leavesBelow →
        (Under (inflatedPosition S D.tree ℓ.toNode) (G.pair x).1 ∨
          Under (inflatedPosition S D.tree (S.pair ℓ).toNode) (G.pair x).1) →
        Below (inflatedPosition S D.tree c) (G.pair x).1 ∨ Below (inflatedPosition S D.tree c') (G.pair x).1 := by
      intro ℓ hℓ hy
      rcases hy with hy | hy
      · exact Or.inl (below_trans (inflatedPosition_below S D.tree c ℓ.toNode ((leafBelow_iff_below _ _).mp hℓ))
          ⟨hy.1.symm, hy.2⟩)
      · have hm := (hcp ℓ (Finset.mem_union_left _ hℓ)).2
        rcases Finset.mem_union.mp hm with hm | hm
        · exact Or.inl (below_trans (inflatedPosition_below S D.tree c _ ((leafBelow_iff_below _ _).mp hm))
            ⟨hy.1.symm, hy.2⟩)
        · exact Or.inr (below_trans (inflatedPosition_below S D.tree c' _ ((leafBelow_iff_below _ _).mp hm))
            ⟨hy.1.symm, hy.2⟩)
    rcases hxe with hxA | hxB
    · have hℓ := leaf_mem_below_of_under D c (p.firstLeaf hS) x.1 hx hxA
      refine reach _ hℓ ?_
      rcases hye with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [← secondLeaf_eq_pair hS p]; exact h)
    · have hℓ := leaf_mem_below_of_under D c (p.secondLeaf hS) x.1 hx hxB
      refine reach _ hℓ ?_
      rcases hye with h | h
      · exact Or.inr (by rw [← firstLeaf_eq_pair hS p]; exact h)
      · exact Or.inl h
  · -- chain attachment
    have hend : ∀ z, z = q.1 ∨ z = q.2 →
        Under (inflatedPosition S D.tree b.toNode) z ∧
        ¬ SUnder (addrExt (inflatedPosition S D.tree b.toNode) (D.tree b).lonePath) z := fun z hz =>
      chain_endpoints_region (D.tree b) _ _ z (Finset.mem_union_right _
        ((mem_pairEndpoints_iff _ _).mpr ⟨q, hb, hz⟩))
    have hxe := hend _ hxq'
    have hye := hend _ hyq
    have hcmp := List.prefix_or_prefix_of_prefix hx.2 hxe.1.2
    rcases hcmp with h | h
    · exact Or.inl (below_trans ⟨hxe.1.1.trans hx.1, h⟩ ⟨hye.1.1.symm, hye.1.2⟩)
    · have hbb : Below (inflatedPosition S D.tree b.toNode) (inflatedPosition S D.tree c) :=
        ⟨hx.1.symm.trans hxe.1.1.symm, h⟩
      have hbc := below_of_pos_below D.tree b.toNode c hbb
      by_cases hcb : b.toNode = c
      · subst hcb
        have hn := hc b rfl
        rw [hn] at hb
        simp [RegChain.pairsAt] at hb
      · exfalso
        obtain ⟨i, hi⟩ := below_child_of_desc_ne b c hbc hcb
        have h1 := inflatedPosition_below S D.tree (b.child i) c hi
        rw [D.core_child_position] at h1
        have h2 := below_trans h1 hx
        apply hxe.2
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · exact h2.1.symm
        · exact (List.prefix_append _ _).trans h2.2
        · intro hxe'
          have := h2.2.length_le
          rw [hxe'] at this
          simp [addrExt, ReconstructionData.corePosition] at this

end WaveTurbulence.LayerCnt
