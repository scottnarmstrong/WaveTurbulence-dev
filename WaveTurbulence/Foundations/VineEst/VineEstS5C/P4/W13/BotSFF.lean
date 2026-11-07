/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.K2.OfContW
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.SFF
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.BotObj

/-! # P4-W1 (bottom): the separated expansions of the bottom bundle (`Bot.BotSepFam`)

The mirror of `SFF` for BOT-DECOMP (R60): at the bottom operative member (piece index `0`, all other members inert: `hup`), the index
`b ∈ botA ∪ botB ⊆ canonFinsetK p kind A c0` carries `botQfam pstar κ A b`, `botTfam pstar κ A b`; the certified expansions `botCertC`,
`botCertT` (`ObjCert` with the window certificates on `winCl/winCh`, `winTl/winTh`, same constants `certCJ`, `certCM`) are built exactly as
`certC`, `certT` (gate level `L₄` for roots `≤ L₄` through `botg_coh_lowC/T`, else `Lₕ` natively), and `botSepFamOf` has `PtOK := True`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W13
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine TTree WaveTurbulence.Twist
  WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj
  WaveTurbulence.Stage1 WaveTurbulence.ConjCoh WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5C.P4.Bot

set_option linter.unusedSectionVars false

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} [Fintype ι] [DecidableEq ι]
variable {P : WTParams} {κ : KPar P.d} {Bh : ℕ → ℝ}

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
  (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4)

include hcan hel htc hcc hA hup in
/-- `n` of a carrier-side couple is at most `zpN A`. -/
theorem botNC_le (b : BT w ι) (hb : b ∈ canonFinsetK p kind A c0) :
    (zpCodeC b.1 pstar).size / 2 ≤ zpN A pstar := by
  have := botg_sizes A c0 hA hcan hel htc hcc hup b hb
  omega

include hcan hel htc hcc hA hup in
theorem botNT_le (b : BT w ι) (hb : b ∈ canonFinsetK p kind A c0) :
    (zpCodeT b.1 pstar).size / 2 ≤ zpN A pstar := by
  have := botg_sizes A c0 hA hcan hel htc hcc hup b hb
  omega

include hcan hel htc hcc hA hup E hN in
/-- The certified couple expansion at a gate level `q ∈ {L₄, Lₕ}`. -/
noncomputable def botCertC_at (b : BT w ι) (hb : b ∈ canonFinsetK p kind A c0) (q : ℕ)
    (hq : q = zpQ4 A pstar ∨ q = zpQh A pstar)
    (hcoh : IsCoherentCoupleAt p q (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar)) :
    ObjCert P (30 * P.d) (botQfam pstar κ A b) (winCl A pstar) (winCh A pstar) (cornL A pstar) (cornH A pstar) :=
  have hL24 := zpQ2_le_zpQ4 A hcan hel htc hcc
  have h4h := zpQ4_le_zpQh A hcan hel htc hcc
  have hhp := zpQh_le_p A hcan hel htc hcc
  have hL2q : zpQ2 A pstar ≤ q := by rcases hq with rfl | rfl <;> omega
  have hqp : q ≤ p := by rcases hq with rfl | rfl <;> omega
  have hn : (zpCodeC b.1 pstar).size / 2 ≤ P.N (p + 1) ^ 4 := (botNC_le A c0 hA hcan hel htc hcc hup b hb).trans hN
  let G := ContExp.gateC (h := κ.F) E.hg E.hB E.hp E.hθ hn hL2q hqp (size_half_cpl _) hcoh
  have hcost : 0 ≤ layerCost Bh (zpObjC b.1 pstar) :=
    layerCost_nonneg _ fun x => (E.hB _ (coherentCouple_layer_le hL2q hqp hcoh x)).1
  W2.K2.ofContW G (fun i => W2.K2.clampSel (q ≤ cplRootLayer (zpObjC b.1 pstar)) (q : ℝ) (G.J i)) (botQfam pstar κ A b)
    (VC q (zpQ4 A pstar) (botLq pstar b) (zpQ2 A pstar))
    (fun t s hts k =>
      ((botQ_expand κ A b (zpQ4 A pstar) hL24 hL2q hqp hcoh (P.δ ^ ((zpCodeC b.1 pstar).size / 2)) G.J G.M
        (fun ts hts k => by rw [E.hδ, G.hexp ts hts k]; push_cast; rfl)) t s hts k).trans
      (W2.K2.sum_clampSel_eq _ _ _ _ t s k (fun hfl htq => by
        obtain ⟨⟨hs1, hs2⟩, hc⟩ := hts
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs1 hs2 hc htq
        rcases hc with hc | ⟨h4, -, -⟩
        · exact absurd hc (not_lt.2 htq.le)
        · have hgt : zpQ2 A pstar < q := by
            have : (zpQ2 A pstar : ℝ) < q :=
              lt_of_le_of_lt (by exact_mod_cast hL24) (lt_trans h4 htq)
            exact_mod_cast this
          exact W2.K2.couple_gate_vanish G hL2q hqp hcoh hgt hfl hs1 hs2 k)).symm)
    (timeBox_subset_cell _ _) (timeBox_subset_closure_interior _ _)
    (timeBox_subset_cell _ _) (timeBox_subset_closure_interior _ _) E.hC E.hη hcost
    (fun i => W2.K2.clampSel_bound_C E.hθ E.hη hL2q (window_case _ _) (G.hJc i)
      (by have := E.hC; positivity) (G.hJ i))
    (fun i => W2.K2.clampSel_bound_C E.hθ E.hη hL2q (window_case _ _) (G.hJc i)
      (by have := E.hC; positivity) (G.hJ i))

include hcan hel htc hcc hA hup E hN in
/-- The certified tree expansion at a gate level `q ∈ {L₄, Lₕ}`. -/
noncomputable def botCertT_at (b : BT w ι) (hb : b ∈ canonFinsetK p kind A c0) (q : ℕ)
    (hq : q = zpQ4 A pstar ∨ q = zpQh A pstar)
    (hcoh : IsCoherentTreeAt p q (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar)) :
    ObjCert P 0 (botTfam pstar κ A b) (winTl A pstar) (winTh A pstar) (cornL A pstar) (cornH A pstar) :=
  have hL24 := zpQ2_le_zpQ4 A hcan hel htc hcc
  have h4h := zpQ4_le_zpQh A hcan hel htc hcc
  have hhp := zpQh_le_p A hcan hel htc hcc
  have hL2q : zpQ2 A pstar ≤ q := by rcases hq with rfl | rfl <;> omega
  have hqp : q ≤ p := by rcases hq with rfl | rfl <;> omega
  have hn : (zpCodeT b.1 pstar).size / 2 ≤ P.N (p + 1) ^ 4 := (botNT_le A c0 hA hcan hel htc hcc hup b hb).trans hN
  let G := ContExp.gateT (h := κ.F) E.hg E.hB E.hp E.hθ hn hL2q hqp (size_half_chain _) hcoh
  have hcost : 0 ≤ layerCost Bh (zpObjT b.1 pstar) :=
    layerCost_nonneg _ fun x => (E.hB _ ((coherentTree_layer_le hL2q hcoh x).trans hqp)).1
  W2.K2.ofContW G (fun i => W2.K2.clampSel (q ≤ treeRootLayer (zpObjT b.1 pstar)) (q : ℝ) (G.J i)) (botTfam pstar κ A b)
    (VT q (zpQ4 A pstar) (botLt pstar b) (zpQ2 A pstar))
    (fun t s hts k =>
      ((botT_expand κ A b (zpQ4 A pstar) hL24 hL2q hcoh (P.δ ^ ((zpCodeT b.1 pstar).size / 2)) G.J G.M
        (fun ts hts k => by rw [E.hδ, G.hexp ts hts k]; push_cast; rfl)) t s hts k).trans
      (W2.K2.sum_clampSel_eq _ _ _ _ t s k (fun hfl htq => by
        obtain ⟨⟨hs1, hs2⟩, hc⟩ := hts
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs1 hs2 hc htq
        rcases hc with ⟨hc, -⟩ | ⟨h4, -, -⟩
        · exact absurd hc (not_lt.2 htq.le)
        · have hgt : zpQ2 A pstar < q := by
            have : (zpQ2 A pstar : ℝ) < q :=
              lt_of_le_of_lt (by exact_mod_cast hL24) (lt_trans h4 htq)
            exact_mod_cast this
          exact W2.K2.tree_gate_vanish G hL2q hcoh hgt hfl hs1 hs2 k)).symm)
    (timeBoxGt_subset_cell _ _) (timeBoxGt_subset_closure_interior (L2_le_L4R A hcan hel htc hcc))
    (timeBoxGt_subset_cell _ _) (timeBoxGt_subset_closure_interior (L2_le_LhR A hcan hel htc hcc)) E.hC E.hη hcost
    (fun i => W2.K2.clampSel_bound_T E.hθ E.hη hL2q hL24 (window_case _ _) (G.hJc i)
      (by have := E.hC; positivity) (G.hJ i))
    (fun i => W2.K2.clampSel_bound_T E.hθ E.hη hL2q (hL24.trans h4h) (window_case _ _) (G.hJc i)
      (by have := E.hC; positivity) (G.hJ i))

include hcan hel htc hcc hA hup E hN in
open Classical in
/-- **The certified couple expansion of every index** (trivial off `botA ∪ botB`). -/
noncomputable def botCertC (b : BT w ι) :
    ObjCert P (30 * P.d) (botQfam pstar κ A b) (winCl A pstar) (winCh A pstar) (cornL A pstar) (cornH A pstar) :=
  if hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0 then
    if hr : cplRootLayer (zpObjC b.1 pstar) ≤ zpQ4 A pstar then
      botCertC_at A c0 hA hcan hel htc hcc hup E hN b (mem_canon_of_botbs A c0 hb) (zpQ4 A pstar) (Or.inl rfl)
        (botg_coh_lowC A c0 hA hcan hel htc hcc hup hb hr)
    else
      botCertC_at A c0 hA hcan hel htc hcc hup E hN b (mem_canon_of_botbs A c0 hb) (zpQQ b.1 pstar).1
        (Or.inr (botg_high_C A c0 hA hcan hel htc hcc hup b (mem_canon_of_botbs A c0 hb) (not_le.1 hr)))
        (botg_nat_cohC A c0 hA hcan hel htc hcc hup b (mem_canon_of_botbs A c0 hb))
  else ObjCert.triv _ (timeBox_subset_cell _ _) (timeBox_subset_closure_interior _ _)
    (timeBox_subset_cell _ _) (timeBox_subset_closure_interior _ _)

include hcan hel htc hcc hA hup E hN in
open Classical in
/-- **The certified tree expansion of every index** (trivial off `botA ∪ botB`). -/
noncomputable def botCertT (b : BT w ι) :
    ObjCert P 0 (botTfam pstar κ A b) (winTl A pstar) (winTh A pstar) (cornL A pstar) (cornH A pstar) :=
  if hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0 then
    if hr : treeRootLayer (zpObjT b.1 pstar) ≤ zpQ4 A pstar then
      botCertT_at A c0 hA hcan hel htc hcc hup E hN b (mem_canon_of_botbs A c0 hb) (zpQ4 A pstar) (Or.inl rfl)
        (botg_coh_lowT A c0 hA hcan hel htc hcc hup hb hr)
    else
      botCertT_at A c0 hA hcan hel htc hcc hup E hN b (mem_canon_of_botbs A c0 hb) (zpBranchQ b.1 pstar).1
        (Or.inr (botg_high_T A c0 hA hcan hel htc hcc hup b (mem_canon_of_botbs A c0 hb) (not_le.1 hr)))
        (botg_nat_cohT A c0 hA hcan hel htc hcc hup b (mem_canon_of_botbs A c0 hb))
  else ObjCert.triv _ (timeBoxGt_subset_cell _ _) (timeBoxGt_subset_closure_interior (L2_le_L4R A hcan hel htc hcc))
    (timeBoxGt_subset_cell _ _) (timeBoxGt_subset_closure_interior (L2_le_LhR A hcan hel htc hcc))

include hcan hel htc hcc hA hup E hN in
/-- **The separated expansions of the bottom bundle** (`Bot.BotSepFam`), with `PtOK := True`. -/
noncomputable def botSepFamOf : BotSepFam p kind pstar A c0 κ where
  S := ⟨fun b => (botCertC A c0 hA hcan hel htc hcc hup E hN b).m, fun b => (botCertT A c0 hA hcan hel htc hcc hup E hN b).m,
    fun b => (botCertC A c0 hA hcan hel htc hcc hup E hN b).term, fun b => (botCertT A c0 hA hcan hel htc hcc hup E hN b).term⟩
  PtOK _ _ _ := True
  hQ _ s1 t1 _ b _ := ⟨fun k => (botCertC A c0 hA hcan hel htc hcc hup E hN b).sum_term s1 _ k,
    fun k => (botCertC A c0 hA hcan hel htc hcc hup E hN b).sum_term t1 _ k⟩
  hT _ s1 t1 _ b _ := ⟨fun k => (botCertT A c0 hA hcan hel htc hcc hup E hN b).sum_term s1 _ k,
    fun k => (botCertT A c0 hA hcan hel htc hcc hup E hN b).sum_term t1 _ k⟩
  dom _ _ _ _ _ := trivial

include hcan hel htc hcc hA hup E hN in
theorem botCertC_at_m_le (b : BT w ι) (hb : b ∈ canonFinsetK p kind A c0) (q : ℕ)
    (hq : q = zpQ4 A pstar ∨ q = zpQh A pstar)
    (hcoh : IsCoherentCoupleAt p q (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar)) :
    (botCertC_at (κ := κ) A c0 hA hcan hel htc hcc hup E hN b hb q hq hcoh).m ≤ 2 ^ ((zpCodeC b.1 pstar).size / 2) := by
  unfold botCertC_at
  exact max_le (ContExp.hm _) Nat.one_le_two_pow

include hcan hel htc hcc hA hup E hN in
theorem botCertT_at_m_le (b : BT w ι) (hb : b ∈ canonFinsetK p kind A c0) (q : ℕ)
    (hq : q = zpQ4 A pstar ∨ q = zpQh A pstar)
    (hcoh : IsCoherentTreeAt p q (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar)) :
    (botCertT_at (κ := κ) A c0 hA hcan hel htc hcc hup E hN b hb q hq hcoh).m ≤ 2 ^ ((zpCodeT b.1 pstar).size / 2) := by
  unfold botCertT_at
  exact max_le (ContExp.hm _) Nat.one_le_two_pow

include hcan hel htc hcc hA hup E hN in
theorem botCertC_m_le (b : BT w ι) : (botCertC A c0 hA hcan hel htc hcc hup E hN b).m ≤ 2 ^ zpN A pstar := by
  classical
  unfold botCertC
  split_ifs with hb hr
  · exact (botCertC_at_m_le A c0 hA hcan hel htc hcc hup E hN _ _ _ _ _).trans
      (Nat.pow_le_pow_right (by norm_num) (botNC_le A c0 hA hcan hel htc hcc hup b (mem_canon_of_botbs A c0 hb)))
  · exact (botCertC_at_m_le A c0 hA hcan hel htc hcc hup E hN _ _ _ _ _).trans
      (Nat.pow_le_pow_right (by norm_num) (botNC_le A c0 hA hcan hel htc hcc hup b (mem_canon_of_botbs A c0 hb)))
  · exact Nat.one_le_two_pow

include hcan hel htc hcc hA hup E hN in
theorem botCertT_m_le (b : BT w ι) : (botCertT A c0 hA hcan hel htc hcc hup E hN b).m ≤ 2 ^ zpN A pstar := by
  classical
  unfold botCertT
  split_ifs with hb hr
  · exact (botCertT_at_m_le A c0 hA hcan hel htc hcc hup E hN _ _ _ _ _).trans
      (Nat.pow_le_pow_right (by norm_num) (botNT_le A c0 hA hcan hel htc hcc hup b (mem_canon_of_botbs A c0 hb)))
  · exact (botCertT_at_m_le A c0 hA hcan hel htc hcc hup E hN _ _ _ _ _).trans
      (Nat.pow_le_pow_right (by norm_num) (botNT_le A c0 hA hcan hel htc hcc hup b (mem_canon_of_botbs A c0 hb)))
  · exact Nat.one_le_two_pow

end WaveTurbulence.VineEstS5C.P4.W13
