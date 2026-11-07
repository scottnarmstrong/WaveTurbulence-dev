/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.ZpGeo
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Family

/-! # P4-W1 (bottom): the parent layers, sizes, coherence and class count of the bottom class `canonFinsetK p kind A c0` (R60, BOT-DECOMP)

The mirror of `ZpGeo` (and of P4's `card_zpFinset_le`) for the index type `Bot.BT` of the bottom bundle: every pair of the bottom class
has as state the output of an operation at the bottom member (`Bot.bot_classify`), so ZP-SURJ's state-level facts apply verbatim
(`op_numbers`, `two_zpN`, `con_excDatum`, coherence, and the carrier through `Bot.BotSurj.carrier`).

* `botg_numbers`, `botg_sizes`, `botg_nat_cohC/T`, `botg_coh_lowC/T`, `botg_high_C/T` (as in `ZpGeo`);
* `card_canonFinset_le`: `#canonFinsetK p kind A c0 ≤ 16 (N+1) (4·12⁹)^N 4^p`, `N = zpN A pstar` (the bottom twin of `card_zpFinset_le`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W13
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine TTree WaveTurbulence.Twist
  WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj
  WaveTurbulence.Stage1 WaveTurbulence.ConjCoh WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P4.Bot

set_option linter.unusedSectionVars false

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} [Fintype ι] [DecidableEq ι]

variable (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family) (hA : IsPrimeGarden A.skeleton)
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
  (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))

include hA hup hcan hel htc hcc

theorem botg_numbers (G : BT w ι) (hG : G ∈ canonFinsetK p kind A c0) :
    (zpQQ G.1 pstar).2 = zpQ2 A pstar ∧ (zpBranchQ G.1 pstar).2 = zpQ2 A pstar ∧
    (((zpQQ G.1 pstar).1 = numR A pstar ∧ (zpBranchQ G.1 pstar).1 = (zpBranchQ A pstar).1) ∨
      ((zpQQ G.1 pstar).1 = (zpBranchQ A pstar).1 ∧ (zpBranchQ G.1 pstar).1 = numR A pstar)) := by
  classical
  obtain ⟨ε, con, he⟩ := bot_classify A hcan hel htc hcc c0 hA hup hG
  obtain ⟨hL2, hnum⟩ := op_numbers A hcan hel htc hcc con
  have hQQ := zpQQ_eq G.1 pstar
  rw [he] at hQQ ⊢
  rw [hQQ]
  refine ⟨hL2, hL2, ?_⟩
  rcases hnum with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h2, h1⟩
  · exact Or.inr ⟨h2, h1⟩

theorem botg_sizes (G : BT w ι) (hG : G ∈ canonFinsetK p kind A c0) :
    (zpCodeC G.1 pstar).size + (zpCodeT G.1 pstar).size = 2 * zpN A pstar := by
  classical
  obtain ⟨ε, con, he⟩ := bot_classify A hcan hel htc hcc c0 hA hup hG
  have hd := zpData_op A hcan hel htc hcc con
  have hsC : (zpCodeC G.1 pstar).size = con.newCouple.size := by
    unfold zpCodeC; rw [he, hd]; split_ifs <;> simp [size_conjCpl]
  have hsT : (zpCodeT G.1 pstar).size = con.newTree.size := by
    unfold zpCodeT; rw [he, hd]; split_ifs <;> simp [size_conjChain]
  have hsum : con.newTree.size + con.newCouple.size = 2 * zpN A pstar := by
    rw [two_zpN A]; exact (con_excDatum con).size
  omega

omit hA hup hcan hel htc hcc in
theorem mem_canon_of_botbs {b : BT w ι} (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) : b ∈ canonFinsetK p kind A c0 := by
  classical
  rcases hb with h | h
  · exact (Finset.mem_filter.mp h).1
  · exact (Finset.mem_filter.mp h).1

omit hA hup hcan hel htc hcc in
theorem neg_of_botbs_rootsLE {b : BT w ι} (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0)
    (hR : ZpRootsLE A b.1 pstar) : nuOf b.1 pstar = -1 := by
  classical
  have hn : nuOf b.1 pstar ≠ 1 := by
    rcases hb with h | h
    · rcases (Finset.mem_filter.mp h).2 with ⟨hn, -⟩ | ⟨-, hr⟩
      · exact hn
      · exact absurd hR hr
    · exact (Finset.mem_filter.mp h).2
  exact (VineEstS5C.units_ne_one_iff _).mp hn

theorem carrier_of_botbs {b : BT w ι} (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) (hR : ZpRootsLE A b.1 pstar) :
    IsCoherentCoupleAt p (zpQ4 A pstar) (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar) ∧
      IsCoherentTreeAt p (zpQ4 A pstar) (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar) := by
  have hZ := botSurj_of_state A hcan hel htc hcc c0 hA hup
  have hm : b ∈ botSet p kind pstar A c0 (-1) :=
    ⟨mem_canon_of_botbs A c0 hb, neg_of_botbs_rootsLE A c0 hb hR, hR⟩
  have hc := hZ.carrier.mapsTo hm
  exact ⟨hc.1, hc.2.1⟩

theorem botg_nat_cohC (G : BT w ι) (hG : G ∈ canonFinsetK p kind A c0) :
    IsCoherentCoupleAt p (zpQQ G.1 pstar).1 (zpQ2 A pstar) (zpCodeC G.1 pstar) (zpObjC G.1 pstar) := by
  have h := ((botSurj_of_state A hcan hel htc hcc c0 hA hup).coherent G hG).1
  rwa [(botg_numbers A c0 hA hcan hel htc hcc hup G hG).1] at h

theorem botg_nat_cohT (G : BT w ι) (hG : G ∈ canonFinsetK p kind A c0) :
    IsCoherentTreeAt p (zpBranchQ G.1 pstar).1 (zpQ2 A pstar) (zpCodeT G.1 pstar) (zpObjT G.1 pstar) := by
  have h := ((botSurj_of_state A hcan hel htc hcc c0 hA hup).coherent G hG).2
  rwa [(botg_numbers A c0 hA hcan hel htc hcc hup G hG).2.1] at h

theorem botg_nat_le (G : BT w ι) (hG : G ∈ canonFinsetK p kind A c0) :
    zpQ4 A pstar ≤ (zpQQ G.1 pstar).1 ∧ (zpQQ G.1 pstar).1 ≤ zpQh A pstar ∧
      zpQ4 A pstar ≤ (zpBranchQ G.1 pstar).1 ∧ (zpBranchQ G.1 pstar).1 ≤ zpQh A pstar ∧
      ((zpQQ G.1 pstar).1 = zpQ4 A pstar ∨ (zpBranchQ G.1 pstar).1 = zpQ4 A pstar) := by
  have hm := zpQ4_eq_min A hcan hel htc hcc
  unfold zpQh
  rcases (botg_numbers A c0 hA hcan hel htc hcc hup G hG).2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, hm] <;>
    refine ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem botg_cplRoot_le_nat (G : BT w ι) (hG : G ∈ canonFinsetK p kind A c0) :
    zpQ2 A pstar ≤ cplRootLayer (zpObjC G.1 pstar) ∧ cplRootLayer (zpObjC G.1 pstar) ≤ (zpQQ G.1 pstar).1 := by
  have hn := botg_nat_le A c0 hA hcan hel htc hcc hup G hG
  have h2 := zpQ2_le_zpQ4 A hcan hel htc hcc
  exact cpl_root_bounds (h2.trans hn.1) ((hn.2.1).trans (zpQh_le_p A hcan hel htc hcc))
    (botg_nat_cohC A c0 hA hcan hel htc hcc hup G hG)

theorem botg_treeRoot_le_nat (G : BT w ι) (hG : G ∈ canonFinsetK p kind A c0) :
    zpQ2 A pstar ≤ treeRootLayer (zpObjT G.1 pstar) ∧ treeRootLayer (zpObjT G.1 pstar) ≤ (zpBranchQ G.1 pstar).1 := by
  have hn := botg_nat_le A c0 hA hcan hel htc hcc hup G hG
  have h2 := zpQ2_le_zpQ4 A hcan hel htc hcc
  obtain ⟨a1, a2, -⟩ := tree_root_bounds (h2.trans hn.2.2.1) (botg_nat_cohT A c0 hA hcan hel htc hcc hup G hG)
  rw [P1.treeRootLayer_eq]
  exact ⟨a1, a2⟩

theorem botg_coh_lowC {b : BT w ι} (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0)
    (hr : cplRootLayer (zpObjC b.1 pstar) ≤ zpQ4 A pstar) :
    IsCoherentCoupleAt p (zpQ4 A pstar) (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar) := by
  have hG := mem_canon_of_botbs A c0 hb
  rcases (botg_nat_le A c0 hA hcan hel htc hcc hup b hG).2.2.2.2 with h | h
  · rw [← h]; exact botg_nat_cohC A c0 hA hcan hel htc hcc hup b hG
  · have ht := (botg_treeRoot_le_nat A c0 hA hcan hel htc hcc hup b hG).2
    rw [h] at ht
    exact (carrier_of_botbs A c0 hA hcan hel htc hcc hup hb ⟨hr, ht⟩).1

theorem botg_coh_lowT {b : BT w ι} (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0)
    (hr : treeRootLayer (zpObjT b.1 pstar) ≤ zpQ4 A pstar) :
    IsCoherentTreeAt p (zpQ4 A pstar) (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar) := by
  have hG := mem_canon_of_botbs A c0 hb
  rcases (botg_nat_le A c0 hA hcan hel htc hcc hup b hG).2.2.2.2 with h | h
  · have hc := (botg_cplRoot_le_nat A c0 hA hcan hel htc hcc hup b hG).2
    rw [h] at hc
    exact (carrier_of_botbs A c0 hA hcan hel htc hcc hup hb ⟨hc, hr⟩).2
  · rw [← h]; exact botg_nat_cohT A c0 hA hcan hel htc hcc hup b hG

theorem botg_high_C (G : BT w ι) (hG : G ∈ canonFinsetK p kind A c0)
    (hr : zpQ4 A pstar < cplRootLayer (zpObjC G.1 pstar)) : (zpQQ G.1 pstar).1 = zpQh A pstar := by
  have hc := (botg_cplRoot_le_nat A c0 hA hcan hel htc hcc hup G hG).2
  have hm := zpQ4_eq_min A hcan hel htc hcc
  unfold zpQh
  rcases (botg_numbers A c0 hA hcan hel htc hcc hup G hG).2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at hc ⊢ <;>
    rw [hm] at hr <;> omega

theorem botg_high_T (G : BT w ι) (hG : G ∈ canonFinsetK p kind A c0)
    (hr : zpQ4 A pstar < treeRootLayer (zpObjT G.1 pstar)) : (zpBranchQ G.1 pstar).1 = zpQh A pstar := by
  have hc := (botg_treeRoot_le_nat A c0 hA hcan hel htc hcc hup G hG).2
  have hm := zpQ4_eq_min A hcan hel htc hcc
  unfold zpQh
  rcases (botg_numbers A c0 hA hcan hel htc hcc hup G hG).2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] at hc ⊢ <;>
    rw [hm] at hr <;> omega

/-- The carrier-side triple of a pair of the bottom class. -/
noncomputable def botTriple (G : BT w ι) : ℤˣ × LayeredGarden 2 × LayeredGarden 1 :=
  (nuOf G.1 pstar, zpObjC G.1 pstar, zpObjT G.1 pstar)

theorem botTriple_mem (G : BT w ι) (hG : G ∈ canonFinsetK p kind A c0) :
    botTriple (pstar := pstar) G ∈ zpTarget p (numR A pstar) (zpBranchQ A pstar).1 (zpBranchQ A pstar).2 (zpN A pstar) := by
  classical
  have hC := botg_nat_cohC A c0 hA hcan hel htc hcc hup G hG
  have hT := botg_nat_cohT A c0 hA hcan hel htc hcc hup G hG
  have hsz := botg_sizes A c0 hA hcan hel htc hcc hup G hG
  obtain ⟨m₁, hm₁⟩ := regCpl_size_even (zpCodeC G.1 pstar)
  obtain ⟨m₂, hm₂⟩ := regChain_size_even (zpCodeT G.1 pstar)
  have hmN : m₁ + m₂ = zpN A pstar := by omega
  have hnum := (botg_numbers A c0 hA hcan hel htc hcc hup G hG).2.2
  have hq1 : (zpQQ G.1 pstar).1 ∈ ({numR A pstar, (zpBranchQ A pstar).1} : Finset ℕ) := by
    rcases hnum with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hq2 : (zpBranchQ G.1 pstar).1 ∈ ({numR A pstar, (zpBranchQ A pstar).1} : Finset ℕ) := by
    rcases hnum with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
  unfold botTriple zpTarget
  refine Finset.mem_product.2 ⟨Finset.mem_univ _, ?_⟩
  refine Finset.mem_biUnion.2 ⟨m₁, Finset.mem_range.2 (by omega), ?_⟩
  refine Finset.mem_biUnion.2 ⟨_, hq1, ?_⟩
  refine Finset.mem_biUnion.2 ⟨_, hq2, ?_⟩
  refine Finset.mem_biUnion.2 ⟨(zpObjT G.1 pstar).garden.sig 0, Finset.mem_univ _, ?_⟩
  refine Finset.mem_product.2 ⟨?_, ?_⟩
  · rw [Set.Finite.mem_toFinset]
    exact Set.mem_iUnion.2 ⟨⟨zpCodeC G.1 pstar, hC.1, by omega⟩, hC⟩
  · rw [Set.Finite.mem_toFinset, show zpN A pstar - m₁ = m₂ by omega]
    exact Set.mem_iUnion.2 ⟨⟨zpCodeT G.1 pstar, hT.1, by omega⟩, hT, rfl⟩

omit hcan hel htc hcc in
theorem botTriple_injOn :
    Set.InjOn (botTriple (w := w) (pstar := pstar)) (canonFinsetK p kind A c0 : Set (BT w ι)) := by
  intro G1 hG1 G2 hG2 he
  have hs : sigStar G1.1 pstar = sigStar G2.1 pstar := by
    rw [sigStar_of_triple G1.1, sigStar_of_triple G2.1]
    unfold botTriple at he
    simp only [Prod.mk.injEq] at he
    rw [he.1, he.2.1, he.2.2]
  exact bt_ext A c0 hA hup hG1 hG2
    (zp_eq_of_sigStar hA ((mem_canonFinset_iff_bottom hA hup).1 hG1).batch ((mem_canonFinset_iff_bottom hA hup).1 hG2).batch hs)

/-- **The bottom class count**: `#canonFinsetK p kind A c0 ≤ 16 (N+1) (4·12⁹)^N 4^p`, `N = zpN A pstar`. -/
theorem card_canonFinset_le :
    (canonFinsetK p kind A c0).card ≤ 16 * (zpN A pstar + 1) * ((4 * 12 ^ 9) ^ zpN A pstar * 4 ^ p) := by
  refine (Finset.card_le_card_of_injOn (botTriple (w := w) (pstar := pstar))
    (fun G hG => botTriple_mem A c0 hA hcan hel htc hcc hup G hG)
    (botTriple_injOn A c0 hA hup)).trans (card_zpTarget_le _ _ _ _ _ ?_ ?_ ?_)
  · exact q1_le_p A pstar hcan hel htc hcc
  · exact q2_le_p A pstar hcan hel htc hcc
  · exact (L2_le_q2 A pstar hcan hel htc hcc).trans (q2_le_p A pstar hcan hel htc hcc)

end WaveTurbulence.VineEstS5C.P4.W13
