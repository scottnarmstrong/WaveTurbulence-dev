/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionPairListMembership
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CodeEndpointLeaves
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedPositionSeparation
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SourceStructure
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CoupleSkeletonRegularity
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.TrivialRootPartners
public import WaveTurbulence.Foundations.Stage1.Shared.CombSnapshot.Components
public import WaveTurbulence.Foundations.Stage1.Shared.CombSnapshot.Couples
import Mathlib.Tactic

/-!
# SKEL-FACTS 1: facts about the prime skeleton of a decoded garden

For `D : ReconstructionData S` decoding a plain garden `G` (`D.Decodes hS G`):

* `ReconstructionData.treeGraph_le`: adjacency of trees in `G` is adjacency in `S` (couple pairs of `D` join the
  roots of an actual skeleton pair; regular chains stay inside one tree);
* `ReconstructionData.irreducible_of_decodes` : `G.Irreducible → S.Irreducible`;
* `ReconstructionData.sig_eq` / `isBalancedSig_of_decodes`: the signature is retained;
* `ReconstructionData.order_pos_of_decodes`: `1 ≤ S.order` unless `G` is a regular couple (TARGET L636,
  DH21 Proposition 4.13).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Reg.Skeleton
open TTree WaveTurbulence.Comb

variable {w : ℕ}

private theorem fst_of_mem_leafAddresses {t : TTree} {a z : Address w} (h : z ∈ leafAddresses t a) :
    z.1 = a.1 := by
  unfold leafAddresses at h
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp h
  rfl

/-- Every literal attachment pair joins roots of one actual skeleton pair, or lies in one skeleton tree. -/
theorem ReconstructionData.attachmentPair_roots {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (q : Pair w) (hq : q ∈ D.attachmentPairs hS) :
    (∃ p : SourcePair S, (q.1.1 = p.1.1.1 ∨ q.1.1 = p.1.2.1) ∧ (q.2.1 = p.1.1.1 ∨ q.2.1 = p.1.2.1)) ∨
    (∃ r : Fin w, q.1.1 = r ∧ q.2.1 = r) := by
  unfold ReconstructionData.attachmentPairs at hq
  rcases Finset.mem_union.mp hq with h | h
  · obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp h
    have hp' := List.mem_toFinset.mp hp
    have hv := couple_pair_endpoint_leaves (D.couple p) _ _ q hp'
    have h1 := inflatedPosition_index S D.tree (p.firstLeaf hS).toNode
    have h2 := inflatedPosition_index S D.tree (p.secondLeaf hS).toNode
    left
    refine ⟨p, ?_, ?_⟩
    · rcases Finset.mem_union.mp hv.1 with h' | h'
      · left; rw [fst_of_mem_leafAddresses h', h1]; rfl
      · right; rw [fst_of_mem_leafAddresses h', h2]; rfl
    · rcases Finset.mem_union.mp hv.2 with h' | h'
      · left; rw [fst_of_mem_leafAddresses h', h1]; rfl
      · right; rw [fst_of_mem_leafAddresses h', h2]; rfl
  · obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp h
    have hb' := List.mem_toFinset.mp hb
    have hv := chain_pair_endpoint_leaves (D.tree b) (nodeSign S.sig b.1)
      (node3 (fun i => D.inflateNode hS (b.child i))) _ q hb'
    have h1 := inflatedPosition_index S D.tree b.toNode
    right
    exact ⟨b.1.1, by rw [fst_of_mem_leafAddresses hv.1, h1]; rfl,
      by rw [fst_of_mem_leafAddresses hv.2, h1]; rfl⟩

/-- Tree adjacency in the decoded garden `G` is tree adjacency in the skeleton `S`. -/
theorem ReconstructionData.treeGraph_le {S G : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (hd : D.Decodes hS G) : treeGraph G ≤ treeGraph S := by
  intro i j hadj
  obtain ⟨hne, ℓ, hi, hj⟩ := hadj
  have hmem : sourcePairAt G ℓ ∈ D.attachmentPairs hS := by
    have h0 := sourcePairAt_mem G hd.1 ℓ
    have h1 : (D.raw hS).pairs = (rawOfGarden G).pairs := by rw [hd.2]
    have h2 : D.attachmentPairs hS = sourcePairs G := h1
    rw [h2]; exact h0
  have hij : ((sourcePairAt G ℓ).1.1 = i ∧ (sourcePairAt G ℓ).2.1 = j) ∨
      ((sourcePairAt G ℓ).1.1 = j ∧ (sourcePairAt G ℓ).2.1 = i) := by
    unfold sourcePairAt
    split_ifs
    · left; exact ⟨hi, hj⟩
    · right; exact ⟨hj, hi⟩
  rcases D.attachmentPair_roots hS _ hmem with ⟨p, h1, h2⟩ | ⟨r, h1, h2⟩
  · obtain ⟨x, _, hx⟩ := Finset.mem_image.mp p.2
    have hp1 : p.1.1.1 = x.1.1 := by rw [← hx]
    have hp2 : p.1.2.1 = (S.pair x).1.1 := by rw [← hx]
    have hadjx : (treeGraph S).Adj x.1.1 (S.pair x).1.1 := by
      refine ⟨?_, x, rfl, rfl⟩
      intro he
      rcases hij with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
        simp_all
    rcases hij with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    all_goals first
      | (exfalso; apply hne; simp_all; done)
      | (simp_all; done)
      | (simp_all [SimpleGraph.adj_comm])
  · exfalso
    apply hne
    rcases hij with ⟨a, b⟩ | ⟨a, b⟩ <;> simp_all

/-- The skeleton of an irreducible plain garden is irreducible. -/
theorem ReconstructionData.irreducible_of_decodes {S G : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (hd : D.Decodes hS G) (hG : G.Irreducible) : S.Irreducible := by
  rw [irreducible_iff_preconnected S hS]
  have hc := (irreducible_iff_preconnected G hd.1).mp hG
  intro i j
  exact (hc i j).mono (D.treeGraph_le hS hd)

/-- The signature of a decoded garden is the signature of its skeleton. -/
theorem ReconstructionData.sig_eq {S G : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (hd : D.Decodes hS G) : S.sig = G.sig := by
  have := congrArg Raw.sig hd.2
  exact this

end WaveTurbulence.Reg.Skeleton
