/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.PL234Draft.P4CodeApp

/-!
# The number of top-layer branching nodes of a labelled carrier

For labels in `[q', q]` with `q' < q`, a labelled chain is its top block `sliceL X ls q` followed by a chain with
labels `< q` (`top_decomp`). The top-layer branching nodes are exactly the link endpoints of the top block
(`card_top`). Hence, with `q ≤ p`:

* `count_lc`, `count_lt`: `topBranchCount = if q = p then (top block).size else 0`;
* `count_low`: a constant layering in layer `q' < p` has no layer-`p` branching node.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

variable {w : ℕ} {q q' : ℕ}

theorem sliceL_lt {d : ℕ} {r : ℕ} : ∀ (X : RegChain) (ls : List ℕ) (u : ℕ), LabOK d X ls u → u < r →
    sliceL X ls r = .nil
  | .nil, _, _, _, _ => rfl
  | .pair .., [], _, h, _ => h.elim
  | .pair m Qr Qg inner rest, l :: ls, u, ⟨_, h2, h3⟩, hu => by
    show (if l = r then _ else _) = _
    rw [ite_eq_right (by omega), sliceL_lt rest ls l h3 (by omega)]

theorem top_decomp (hlt : q' < q) : ∀ (X : RegChain) (ls : List ℕ), LabOK q' X ls q →
    ∃ T R lsR, X = appendChain T R ∧ ls = List.replicate (topCount T) q ++ lsR ∧ LabOK q' R lsR (q - 1) ∧
      sliceL X ls q = T
  | .nil, ls, h => ⟨.nil, .nil, [], rfl, by rw [show ls = [] from h]; rfl, rfl, rfl⟩
  | .pair .., [], h => h.elim
  | .pair m Qr Qg inner rest, l :: ls, ⟨h1, h2, h3⟩ => by
    by_cases hl : l = q
    · obtain ⟨T, R, lsR, e1, e2, e3, e4⟩ := top_decomp hlt rest ls (hl ▸ h3)
      refine ⟨.pair m Qr Qg inner T, R, lsR, by rw [e1]; rfl, by rw [e2, hl]; rfl, e3, ?_⟩
      show (if l = q then _ else _) = _
      rw [ite_eq_left hl, e4]
    · have hL' : LabOK q' (.pair m Qr Qg inner rest) (l :: ls) (q - 1) := ⟨h1, by omega, h3⟩
      exact ⟨.nil, .pair m Qr Qg inner rest, l :: ls, rfl, rfl, hL',
        sliceL_lt (.pair m Qr Qg inner rest) (l :: ls) (q - 1) hL' (by omega)⟩

theorem chainLay_top {d : ℕ} (R : RegChain) (lsR : List ℕ) : ∀ (T : RegChain) (ζ : ℤˣ) (a z : Fin w × Path),
    z ∈ chainNodesSet T ζ a → chainLay (appendChain T R) (List.replicate (topCount T) q ++ lsR) d a z = q
  | .nil, _, _, z, hz => by simp [chainNodesSet, RegChain.linksAt, RegChain.pairsAt] at hz
  | .pair m Qr Qg inner rest, ζ, a, z, hz => by
    show chainLay (.pair m Qr Qg inner (appendChain rest R)) (q :: (List.replicate (topCount rest) q ++ lsR)) d a z = q
    rcases ownPart_of_mem hz with ho | hr
    · exact chainLay_own ho
    · rw [chainLay_pair, ite_eq_left (chainNodes_region rest _ _ z hr).1]
      exact chainLay_top R lsR rest _ _ z hr

theorem chainLay_below {d : ℕ} (R : RegChain) (lsR : List ℕ) : ∀ (T : RegChain) (a z : Fin w × Path),
    Under (addrExt a T.lonePath) z →
    chainLay (appendChain T R) (List.replicate (topCount T) q ++ lsR) d a z = chainLay R lsR d (addrExt a T.lonePath) z
  | .nil, a, z, _ => by simp [appendChain, addrExt, topCount, RegChain.lonePath]
  | .pair m Qr Qg inner rest, a, z, h => by
    rw [lone_eq] at h ⊢
    show chainLay (.pair m Qr Qg inner (appendChain rest R)) (q :: (List.replicate (topCount rest) q ++ lsR)) d a z = _
    rw [chainLay_pair, ite_eq_left (under_trans (under_ext _ _) h)]
    exact chainLay_below R lsR rest _ z h

theorem card_links (T : RegChain) (ζ : ℤˣ) (a : Fin w × Path) : (pairEndpoints (T.linksAt ζ a)).card = T.size := by
  have h := chain_branchAddresses T ζ .leaf a
  rw [branchAddresses_leaf, Finset.union_empty] at h
  rw [← h, card_branchAddresses, code_plug_order, TTree.order, add_zero]

/-- **The top-layer branching nodes of a labelled chain are the link endpoints of its top block.** -/
theorem card_top (hlt : q' < q) {X : RegChain} {ls : List ℕ} (hL : LabOK q' X ls q) (ζ : ℤˣ) (H : TTree)
    (a : Fin w × Path) :
    ((branchAddresses (X.plug ζ H) a).filter (fun z => chainLay X ls q' a z = q)).card = (sliceL X ls q).size := by
  obtain ⟨T, R, lsR, rfl, rfl, hR, hT⟩ := top_decomp hlt X ls hL
  rw [hT, appendChain_plug, chain_branchAddresses T ζ (R.plug ζ H) a, Finset.filter_union,
    Finset.filter_true_of_mem fun z hz => chainLay_top R lsR T ζ a z (Finset.mem_union_left _ hz),
    Finset.filter_false_of_mem fun z hz => ?_, Finset.union_empty, card_links]
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hz
  rw [chainLay_below R lsR T a _ (under_ext _ _)]
  have := chainLay_le R lsR (q - 1) (addrExt a T.lonePath) (addrExt (addrExt a T.lonePath) u) hR (by omega)
  omega

/-- **The top-layer count of a labelled couple.** -/
theorem count_lc {Xp Xm : RegChain} {Qlp : RegCpl} {ls : List ℕ} {p : ℕ} (h : LabOK q' Xp ls q ∧ q' ≤ q)
    (hlt : q' < q) (hqp : q ≤ p) :
    topBranchCount (lcLG Xp Xm Qlp ls q q') p = if q = p then (sliceL Xp ls q).size else 0 := by
  rw [lcLG_eq h]
  unfold topBranchCount
  simp only
  by_cases hq : q = p
  · subst hq
    rw [ite_eq_left rfl, ← card_top hlt h.1 1 Qlp.trees.1 ((0 : Fin 2), [])]
    refine Finset.card_bij (fun b _ => b.1) (fun b hb => ?_) (fun b₁ _ b₂ _ he => Subtype.ext he) (fun z hz => ?_)
    · have hb' : lcLayer Xp ls q' b.1 = q := (Finset.mem_filter.1 hb).2
      have h0 : b.1.1 = 0 := by
        by_contra h0
        unfold lcLayer at hb'
        rw [ite_eq_right h0] at hb'
        omega
      refine Finset.mem_filter.2 ⟨?_, ?_⟩
      · have hm : b.1.2 ∈ ((decodedCouple (.type2 Xp Xm Qlp)).tree b.1.1).branching := b.2
        rw [h0, (decodedCouple_decodes _).2.1] at hm
        exact Finset.mem_image.2 ⟨b.1.2, hm, Prod.ext h0.symm rfl⟩
      · rw [← lcLayer_chain (z := b.1) ⟨h0.symm, List.nil_prefix⟩]
        exact hb'
    · obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
      obtain ⟨path, hp, rfl⟩ := Finset.mem_image.1 hz1
      have hp' : path ∈ ((decodedCouple (.type2 Xp Xm Qlp)).tree 0).branching := by
        rw [(decodedCouple_decodes _).2.1]
        exact hp
      refine ⟨⟨((0 : Fin 2), path), hp'⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      show lcLayer Xp ls q' ((0 : Fin 2), path) = q
      rw [lcLayer_chain (z := ((0 : Fin 2), path)) ⟨rfl, List.nil_prefix⟩]
      exact hz2
  · rw [ite_eq_right hq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro b _ hb
    have hle : lcLayer Xp ls q' b.1 ≤ q := by
      unfold lcLayer
      split_ifs
      · exact chainLay_le Xp ls q _ _ h.1 h.2
      · exact h.2
    have : lcLayer Xp ls q' b.1 = p := hb
    omega

/-- **The top-layer count of a labelled tree.** -/
theorem count_lt {X : RegChain} {μ : List ℕ} {p : ℕ} (h : LabOK q' X μ q ∧ q' ≤ q) (hlt : q' < q) (hqp : q ≤ p) :
    topBranchCount (ltLG X μ q q') p = if q = p then (sliceL X μ q).size else 0 := by
  rw [ltLG_eq h]
  unfold topBranchCount
  simp only
  by_cases hq : q = p
  · subst hq
    rw [ite_eq_left rfl, ← card_top hlt h.1 1 .leaf ((0 : Fin 2), [])]
    refine Finset.card_bij (fun b _ => treeIota b.1) (fun b hb => ?_)
      (fun b₁ _ b₂ _ he => Subtype.ext (Prod.ext (Subsingleton.elim _ _)
        (show (treeIota b₁.1).2 = (treeIota b₂.1).2 from congrArg Prod.snd he))) (fun z hz => ?_)
    · have hb' : ltLayer X μ q' b.1 = q := (Finset.mem_filter.1 hb).2
      refine Finset.mem_filter.2 ⟨?_, hb'⟩
      have hm : b.1.2 ∈ ((decodedTree X 1).tree b.1.1).branching := b.2
      rw [Subsingleton.elim b.1.1 0, (decodedTree_decodes X 1).1] at hm
      exact Finset.mem_image.2 ⟨b.1.2, hm, rfl⟩
    · obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
      obtain ⟨path, hp, rfl⟩ := Finset.mem_image.1 hz1
      have hp' : path ∈ ((decodedTree X 1).tree 0).branching := by
        rw [(decodedTree_decodes X 1).1]
        exact hp
      exact ⟨⟨((0 : Fin 1), path), hp'⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hz2⟩, rfl⟩
  · rw [ite_eq_right hq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro b _ hb
    have hle : ltLayer X μ q' b.1 ≤ q := chainLay_le X μ q _ _ h.1 h.2
    have : ltLayer X μ q' b.1 = p := hb
    omega

theorem count_low {Q : RegCpl} {p : ℕ} (hlt : q' < q) (hqp : q ≤ p) :
    topBranchCount (constLayered (decodedCouple Q) q') p = 0 := by
  rw [topBranchCount_const, ite_eq_right (by omega)]

end WaveTurbulence.PL234
