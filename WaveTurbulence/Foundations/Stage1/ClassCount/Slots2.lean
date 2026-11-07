/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.Slots
public import WaveTurbulence.Foundations.IncohInst.Links.Coherence
public import WaveTurbulence.Foundations.IncohInst.Links.TreeLinks
public import WaveTurbulence.Foundations.FinalCount.RedSpliceGreg
import Mathlib.Tactic

/-!
# CLASSCOUNT: the slot incoherency is the `gregOf` summand

For an embedded regular couple/tree, the list of links has no repetition and its endpoints are branching nodes, so
`LayeredGarden.incoherency` (a count of branch pairs) agrees with `incohCount` (a count along the list).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree LFTwist RegRed

variable {w : ℕ}

theorem couple_linksAt_flat_nodup (Q : RegCpl) (a b : Fin w × Path) (hab : Indep a b) :
    (flatPairs (Q.linksAt a b)).Nodup := by
  apply nodup_of_card
  rw [flatPairs_toFinset, flatPairs_length, ← couple_branchAddresses,
    Finset.card_union_of_disjoint, card_branchAddresses, card_branchAddresses, code_trees_order]
  · have := couple_linksAt_length Q a b
    omega
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [branchAddresses, Finset.mem_image, addrExt] at hx hx'
    obtain ⟨p, -, rfl⟩ := hx
    obtain ⟨q, -, h⟩ := hx'
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rcases List.append_eq_append_iff.1 h2 with ⟨c, hc, -⟩ | ⟨c, hc, -⟩
    · exact hab.2 ⟨h1, hc ▸ ⟨c, rfl⟩⟩
    · exact hab.1 ⟨h1.symm, hc ▸ ⟨c, rfl⟩⟩

theorem chain_linksAt_flat_nodup (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    (flatPairs (X.linksAt ζ a)).Nodup := by
  apply nodup_of_card
  have := chain_branchAddresses X ζ .leaf a
  rw [branchAddresses_leaf, Finset.union_empty] at this
  rw [flatPairs_toFinset, flatPairs_length, ← this, card_branchAddresses,
    code_plug_order, TTree.order, add_zero]
  have := chain_linksAt_length X ζ a
  omega

theorem embeds_links_branching {G : Garden w} {Q : RegCpl} {a b : Fin w × Path} (hE : Embeds G Q a b)
    {l : (Fin w × Path) × (Fin w × Path)} (hl : l ∈ Q.linksAt a b) :
    l.1.2 ∈ (G.tree l.1.1).branching ∧ l.2.2 ∈ (G.tree l.2.1).branching := by
  have key : ∀ x ∈ pairEndpoints (Q.linksAt a b), x.2 ∈ (G.tree x.1).branching := by
    intro x hx
    rw [← couple_branchAddresses] at hx
    rcases Finset.mem_union.1 hx with h | h
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 h
      exact ((node_iff_of_subtree hE.nodeA hE.treeA q).2.2).2 hq
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 h
      exact ((node_iff_of_subtree hE.nodeB hE.treeB q).2.2).2 hq
  exact ⟨key _ ((mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inl rfl⟩),
    key _ ((mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inr rfl⟩)⟩

theorem chainEmb_links_branching {G : Garden w} {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {h : TTree}
    (hC : ChainEmb G X ζ a h) {l : (Fin w × Path) × (Fin w × Path)} (hl : l ∈ X.linksAt ζ a) :
    l.1.2 ∈ (G.tree l.1.1).branching ∧ l.2.2 ∈ (G.tree l.2.1).branching := by
  have key : ∀ x ∈ pairEndpoints (X.linksAt ζ a), x.2 ∈ (G.tree x.1).branching := by
    intro x hx
    have h1 : x ∈ branchAddresses (X.plug ζ h) a := by
      rw [chain_branchAddresses]; exact Finset.mem_union_left _ hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 h1
    exact ((node_iff_of_subtree hC.node hC.tree q).2.2).2 hq
  exact ⟨key _ ((mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inl rfl⟩),
    key _ ((mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inr rfl⟩)⟩

variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)

/-- The slot incoherency (counted along the link list) is the summand of `gregOf`. -/
theorem slotInc_eq {LG : LayeredGarden w} (hd : D.Decodes hS LG.garden) (s : ReplacementSlot S) :
    LG.incoherency (match s with
      | .inl p => (D.couple p).linksAt (cplA D hS p) (cplB D hS p)
      | .inr b => (D.tree b).linksAt (nodeSign S.sig b.1) (treeA D b)) = slotInc D hS LG s := by
  cases s with
  | inl p =>
    have hE := reconstruction_coupleEmb D hS hd p
    exact incoherency_eq_count_of LG _ (nodup_of_flat_nodup (couple_linksAt_flat_nodup _ _ _ hE.indep))
      (fun l hl => embeds_links_branching hE hl)
  | inr b =>
    have hC := reconstruction_chainEmb D hS hd b
    exact incoherency_eq_count_of LG _ (nodup_of_flat_nodup (chain_linksAt_flat_nodup _ _ _))
      (fun l hl => chainEmb_links_branching hC hl)

/-- `gregOf` is the sum of the slot incoherencies. -/
theorem gregOf_eq_sum {LG : LayeredGarden w} (hd : D.Decodes hS LG.garden) :
    RedSplice.gregOf D hS LG = ∑ s, slotInc D hS LG s := by
  classical
  rw [Fintype.sum_sum_type]
  unfold RedSplice.gregOf
  congr 1
  · refine Finset.sum_congr rfl fun p _ => ?_
    exact slotInc_eq D hS hd (.inl p)
  · refine Finset.sum_congr rfl fun b _ => ?_
    exact slotInc_eq D hS hd (.inr b)

/-- The core layering of `LG` (any value if `LG` is not decoded by `D`). -/
noncomputable def coreOf (LG : LayeredGarden w) : GBranch S.tree → ℕ := by
  classical
  exact if h : D.Decodes hS LG.garden then coreLayer LG D hS h else fun _ => 0

theorem coreOf_eq {LG : LayeredGarden w} (hd : D.Decodes hS LG.garden) :
    coreOf D hS LG = coreLayer LG D hS hd := by
  unfold coreOf; rw [dif_pos hd]

theorem prod_slotBound (p : ℕ) (f : GBranch S.tree → ℕ) (gs : ReplacementSlot S → ℕ) :
    ∏ s, slotBound D hS p f (gs s) s =
      (2 ^ (9 * p)) ^ (∑ s, gs s) * 2 ^ D.size * 2 ^ (∑ s, slotDist hS p f s) := by
  have h1 : ∀ s, slotBound D hS p f (gs s) s =
      (2 ^ (9 * p)) ^ (gs s) * 2 ^ (match s with | .inl pr => (D.couple pr).size | .inr b => (D.tree b).size) *
        2 ^ slotDist hS p f s := by
    intro s; cases s <;> rfl
  simp only [h1]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
    Finset.prod_pow_eq_pow_sum]
  have : (∑ s : ReplacementSlot S, (match s with | .inl pr => (D.couple pr).size | .inr b => (D.tree b).size)) =
      D.size := by
    rw [Fintype.sum_sum_type, ReconstructionData.size]
    simp only [add_comm]
  rw [this]

/-- **Class bound.**  Layered gardens decoded by `D` with a common slot-incoherency vector `gs`. -/
theorem card_class_le (p : ℕ) (gs : ReplacementSlot S → ℕ) (A : Finset (LayeredGarden w))
    (hA : ∀ LG ∈ A, LG.CanonCriterion p ∧ LG.garden.IsPlain ∧ D.Decodes hS LG.garden ∧
      ∀ s, slotInc D hS LG s = gs s) :
    (A.card : ℝ) ≤ (2 ^ (9 * p) : ℝ) ^ (∑ s, gs s) * 2 ^ D.size *
      ∑ f ∈ A.image (coreOf D hS), (2 : ℝ) ^ (∑ s, slotDist hS p f s) := by
  classical
  have hfib : A.card = ∑ f ∈ A.image (coreOf D hS), (A.filter (fun LG => coreOf D hS LG = f)).card :=
    Finset.card_eq_sum_card_image (coreOf D hS) A
  have hb : ∀ f ∈ A.image (coreOf D hS), ((A.filter (fun LG => coreOf D hS LG = f)).card : ℝ) ≤
      (2 ^ (9 * p) : ℝ) ^ (∑ s, gs s) * 2 ^ D.size * (2 : ℝ) ^ (∑ s, slotDist hS p f s) := by
    intro f _
    have h := card_slot_bound D hS p f gs (A.filter (fun LG => coreOf D hS LG = f)) (by
      intro LG hLG
      obtain ⟨hLA, hf⟩ := Finset.mem_filter.1 hLG
      obtain ⟨hc, hp, hd, hinc⟩ := hA LG hLA
      exact ⟨hc, hp, hd, by rw [← coreOf_eq D hS hd]; exact hf, hinc⟩)
    rw [prod_slotBound] at h
    exact_mod_cast h
  rw [hfib, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun f hf => ?_
  exact hb f hf

end WaveTurbulence.ClassCount
