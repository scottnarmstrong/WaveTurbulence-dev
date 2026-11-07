/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.ZpCount

/-! # P4-W1: the parent layers and the coherence of the objects of the states of `Zp(A)` (TARGET L1893-L1925)

At an operative member `pstar` of a state `A` (operation preconditions `hcan hel htc hcc`), write `q₁ = numR A` (parent layer of the
partner of the retained leaf), `q₂ = (zpBranchQ A).1` (parent layer of the lower joint), `L₂ = zpQ2 A`, `L₄ = zpQ4 A = min q₁ q₂` and
`Lₕ = zpQh A = max q₁ q₂`.  For every state `G ∈ Zp(A)`:

* `zp_numbers`: the parent layers of its carrier-side couple and tree are `(q₁, L₂), (q₂, L₂)` or `(q₂, L₂), (q₁, L₂)` (ZP-SURJ `op_numbers`);
* `zp_sizes`: `size (code of couple) + size (code of tree) = 2 zpN A`;
* `zp_coh_lowC` / `zp_coh_lowT`: for `G` in the index set `bsA ∪ bsB` of the bundle, an object with root layer `≤ L₄` is coherent at
  `(L₄, L₂)`: natively if its parent is `L₄`, otherwise `G` has both roots `≤ L₄`, is a II-b state, and the carrier (`ZpSurj.carrier`)
  gives the coherence at `(L₄, L₂)`;
* `zp_coh_highC` / `zp_coh_highT`: an object with root layer `> L₄` has native parent `Lₕ > L₄` and is coherent at `(Lₕ, L₂)`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W13
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine TTree WaveTurbulence.Twist
  WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj
  WaveTurbulence.Stage1 WaveTurbulence.ConjCoh WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1

set_option linter.unusedSectionVars false

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι]

/-- `Lₕ = max (q₁, q₂)`: the larger of the two parent layers of the exceptional pair. -/
noncomputable def zpQh (A : FamilyReconstruction w ι) (pstar : ι) : ℕ := max (numR A pstar) (zpBranchQ A pstar).1

variable (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton)
  (hcan : CanonicalObject p kind A.layered)
  (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement pstar) (A.family.kind pstar)
    (A.family.atoms pstar) (A.family.upper pstar))
  (htc : CohOn A.layered ((A.data.tree (A.family.placement pstar).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement pstar).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement pstar).lower.toNode)))
  (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).secondLeaf A.plain).toNode)))

include hcan hel htc hcc

theorem zpQ4_eq_min : zpQ4 A pstar = min (numR A pstar) (zpBranchQ A pstar).1 := by
  rw [ZpSurj.zpQ4_eq A, max_eq_left (L2_le_q1 A pstar hcan hel htc hcc)]

theorem zpQ2_le_zpQ4 : zpQ2 A pstar ≤ zpQ4 A pstar := by
  rw [zpQ4_eq_min A hcan hel htc hcc]
  exact le_min (L2_le_q1 A pstar hcan hel htc hcc) (L2_le_q2 A pstar hcan hel htc hcc)

theorem zpQ4_le_zpQh : zpQ4 A pstar ≤ zpQh A pstar := by
  rw [zpQ4_eq_min A hcan hel htc hcc]; exact min_le_max

theorem zpQh_le_p : zpQh A pstar ≤ p :=
  max_le (q1_le_p A pstar hcan hel htc hcc) (q2_le_p A pstar hcan hel htc hcc)

/-- **The parent layers of the carrier-side objects of a state of `Zp(A)`.** -/
theorem zp_numbers (G : ST w ι pstar J) (hG : G ∈ zpFinset p kind pstar J A sp0 hA) :
    (zpQQ G.1 pstar).2 = zpQ2 A pstar ∧ (zpBranchQ G.1 pstar).2 = zpQ2 A pstar ∧
    (((zpQQ G.1 pstar).1 = numR A pstar ∧ (zpBranchQ G.1 pstar).1 = (zpBranchQ A pstar).1) ∨
      ((zpQQ G.1 pstar).1 = (zpBranchQ A pstar).1 ∧ (zpBranchQ G.1 pstar).1 = numR A pstar)) := by
  classical
  obtain ⟨ε, con, he⟩ := classify A hcan hel htc hcc hA ((mem_zpFinset hA).1 hG).batch
  obtain ⟨hL2, hnum⟩ := op_numbers A hcan hel htc hcc con
  have hQQ := zpQQ_eq G.1 pstar
  rw [he] at hQQ ⊢
  rw [hQQ]
  refine ⟨hL2, hL2, ?_⟩
  rcases hnum with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h2, h1⟩
  · exact Or.inr ⟨h2, h1⟩

/-- The sizes of the carrier-side codes of a state of `Zp(A)` add up to `2 zpN A`. -/
theorem zp_sizes (G : ST w ι pstar J) (hG : G ∈ zpFinset p kind pstar J A sp0 hA) :
    (zpCodeC G.1 pstar).size + (zpCodeT G.1 pstar).size = 2 * zpN A pstar := by
  classical
  obtain ⟨ε, con, he⟩ := classify A hcan hel htc hcc hA ((mem_zpFinset hA).1 hG).batch
  have hd := zpData_op A hcan hel htc hcc con
  have hsC : (zpCodeC G.1 pstar).size = con.newCouple.size := by
    unfold zpCodeC; rw [he, hd]; split_ifs <;> simp [size_conjCpl]
  have hsT : (zpCodeT G.1 pstar).size = con.newTree.size := by
    unfold zpCodeT; rw [he, hd]; split_ifs <;> simp [size_conjChain]
  have hsum : con.newTree.size + con.newCouple.size = 2 * zpN A pstar := by
    rw [two_zpN A]; exact (con_excDatum con).size
  omega

omit hcan hel htc hcc in
theorem mem_zpFinset_of_bs {b : ST w ι pstar J}
    (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) : b ∈ zpFinset p kind pstar J A sp0 hA := by
  classical
  rcases hb with h | h
  · exact (Finset.mem_filter.mp h).1
  · exact (Finset.mem_filter.mp h).1

omit hcan hel htc hcc in
/-- A state of `bsA ∪ bsB` with both roots `≤ L₄` is a II-b state. -/
theorem neg_of_bs_rootsLE {b : ST w ι pstar J}
    (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) (hR : ZpRootsLE A b.1 pstar) : nuOf b.1 pstar = -1 := by
  classical
  have hn : nuOf b.1 pstar ≠ 1 := by
    rcases hb with h | h
    · rcases (Finset.mem_filter.mp h).2 with ⟨hn, -⟩ | ⟨-, hr⟩
      · exact hn
      · exact absurd hR hr
    · exact (Finset.mem_filter.mp h).2
  exact (units_ne_one_iff _).mp hn

/-- The carrier of a II-b state with roots `≤ L₄`: coherent couple and tree at `(L₄, L₂)`. -/
theorem carrier_of_bs {b : ST w ι pstar J}
    (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) (hR : ZpRootsLE A b.1 pstar) :
    IsCoherentCoupleAt p (zpQ4 A pstar) (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar) ∧
      IsCoherentTreeAt p (zpQ4 A pstar) (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar) := by
  have hZ := zpSurj_of_state A sp0 hA hcan hel htc hcc
  have hm : b ∈ zpSet p kind pstar J A sp0 hA (-1) :=
    ⟨mem_zpFinset_of_bs A sp0 hA hb, neg_of_bs_rootsLE A sp0 hA hb hR, hR⟩
  have hc := hZ.carrier.mapsTo hm
  exact ⟨hc.1, hc.2.1⟩

/-- Native coherence of the couple of a state, at `((zpQQ G).1, L₂)`. -/
theorem nat_cohC (G : ST w ι pstar J) (hG : G ∈ zpFinset p kind pstar J A sp0 hA) :
    IsCoherentCoupleAt p (zpQQ G.1 pstar).1 (zpQ2 A pstar) (zpCodeC G.1 pstar) (zpObjC G.1 pstar) := by
  have h := ((zpSurj_of_state A sp0 hA hcan hel htc hcc).coherent G hG).1
  rwa [(zp_numbers A sp0 hA hcan hel htc hcc G hG).1] at h

/-- Native coherence of the tree of a state, at `((zpBranchQ G).1, L₂)`. -/
theorem nat_cohT (G : ST w ι pstar J) (hG : G ∈ zpFinset p kind pstar J A sp0 hA) :
    IsCoherentTreeAt p (zpBranchQ G.1 pstar).1 (zpQ2 A pstar) (zpCodeT G.1 pstar) (zpObjT G.1 pstar) := by
  have h := ((zpSurj_of_state A sp0 hA hcan hel htc hcc).coherent G hG).2
  rwa [(zp_numbers A sp0 hA hcan hel htc hcc G hG).2.1] at h

theorem nat_le (G : ST w ι pstar J) (hG : G ∈ zpFinset p kind pstar J A sp0 hA) :
    zpQ4 A pstar ≤ (zpQQ G.1 pstar).1 ∧ (zpQQ G.1 pstar).1 ≤ zpQh A pstar ∧
      zpQ4 A pstar ≤ (zpBranchQ G.1 pstar).1 ∧ (zpBranchQ G.1 pstar).1 ≤ zpQh A pstar ∧
      ((zpQQ G.1 pstar).1 = zpQ4 A pstar ∨ (zpBranchQ G.1 pstar).1 = zpQ4 A pstar) := by
  have hm := zpQ4_eq_min A hcan hel htc hcc
  unfold zpQh
  rcases (zp_numbers A sp0 hA hcan hel htc hcc G hG).2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, hm] <;>
    refine ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem cplRoot_le_nat (G : ST w ι pstar J) (hG : G ∈ zpFinset p kind pstar J A sp0 hA) :
    zpQ2 A pstar ≤ cplRootLayer (zpObjC G.1 pstar) ∧ cplRootLayer (zpObjC G.1 pstar) ≤ (zpQQ G.1 pstar).1 := by
  have hn := nat_le A sp0 hA hcan hel htc hcc G hG
  have h2 := zpQ2_le_zpQ4 A hcan hel htc hcc
  exact cpl_root_bounds (h2.trans hn.1) ((hn.2.1).trans (zpQh_le_p A hcan hel htc hcc))
    (nat_cohC A sp0 hA hcan hel htc hcc G hG)

theorem treeRoot_le_nat (G : ST w ι pstar J) (hG : G ∈ zpFinset p kind pstar J A sp0 hA) :
    zpQ2 A pstar ≤ treeRootLayer (zpObjT G.1 pstar) ∧ treeRootLayer (zpObjT G.1 pstar) ≤ (zpBranchQ G.1 pstar).1 := by
  have hn := nat_le A sp0 hA hcan hel htc hcc G hG
  have h2 := zpQ2_le_zpQ4 A hcan hel htc hcc
  obtain ⟨a1, a2, -⟩ := tree_root_bounds (h2.trans hn.2.2.1) (nat_cohT A sp0 hA hcan hel htc hcc G hG)
  rw [P1.treeRootLayer_eq]
  exact ⟨a1, a2⟩

/-- **Low couple**: root `≤ L₄` gives coherence at `(L₄, L₂)`. -/
theorem zp_coh_lowC {b : ST w ι pstar J} (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA)
    (hr : cplRootLayer (zpObjC b.1 pstar) ≤ zpQ4 A pstar) :
    IsCoherentCoupleAt p (zpQ4 A pstar) (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar) := by
  have hG := mem_zpFinset_of_bs A sp0 hA hb
  rcases (nat_le A sp0 hA hcan hel htc hcc b hG).2.2.2.2 with h | h
  · rw [← h]; exact nat_cohC A sp0 hA hcan hel htc hcc b hG
  · have ht := (treeRoot_le_nat A sp0 hA hcan hel htc hcc b hG).2
    rw [h] at ht
    exact (carrier_of_bs A sp0 hA hcan hel htc hcc hb ⟨hr, ht⟩).1

/-- **Low tree**: root `≤ L₄` gives coherence at `(L₄, L₂)`. -/
theorem zp_coh_lowT {b : ST w ι pstar J} (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA)
    (hr : treeRootLayer (zpObjT b.1 pstar) ≤ zpQ4 A pstar) :
    IsCoherentTreeAt p (zpQ4 A pstar) (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar) := by
  have hG := mem_zpFinset_of_bs A sp0 hA hb
  rcases (nat_le A sp0 hA hcan hel htc hcc b hG).2.2.2.2 with h | h
  · have hc := (cplRoot_le_nat A sp0 hA hcan hel htc hcc b hG).2
    rw [h] at hc
    exact (carrier_of_bs A sp0 hA hcan hel htc hcc hb ⟨hc, hr⟩).2
  · rw [← h]; exact nat_cohT A sp0 hA hcan hel htc hcc b hG

/-- **High couple**: root `> L₄` forces the native parent `Lₕ > L₄`. -/
theorem zp_high_C (G : ST w ι pstar J) (hG : G ∈ zpFinset p kind pstar J A sp0 hA)
    (hr : zpQ4 A pstar < cplRootLayer (zpObjC G.1 pstar)) : (zpQQ G.1 pstar).1 = zpQh A pstar := by
  have hn := nat_le A sp0 hA hcan hel htc hcc G hG
  have hc := (cplRoot_le_nat A sp0 hA hcan hel htc hcc G hG).2
  have hm := zpQ4_eq_min A hcan hel htc hcc
  unfold zpQh
  rcases (zp_numbers A sp0 hA hcan hel htc hcc G hG).2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at hc ⊢ <;> rw [hm] at hr <;> omega

/-- **High tree**: root `> L₄` forces the native parent `Lₕ > L₄`. -/
theorem zp_high_T (G : ST w ι pstar J) (hG : G ∈ zpFinset p kind pstar J A sp0 hA)
    (hr : zpQ4 A pstar < treeRootLayer (zpObjT G.1 pstar)) : (zpBranchQ G.1 pstar).1 = zpQh A pstar := by
  have hc := (treeRoot_le_nat A sp0 hA hcan hel htc hcc G hG).2
  have hm := zpQ4_eq_min A hcan hel htc hcc
  unfold zpQh
  rcases (zp_numbers A sp0 hA hcan hel htc hcc G hG).2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] at hc ⊢ <;> rw [hm] at hr <;> omega

end WaveTurbulence.VineEstS5C.P4.W13
