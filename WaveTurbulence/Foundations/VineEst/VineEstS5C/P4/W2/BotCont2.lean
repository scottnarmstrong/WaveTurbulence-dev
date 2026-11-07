/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxCont
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.BotSFF
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.BotGeo

/-! # P4-W2 (bottom, session 9) AUX (a''): continuity of the certified time factors `botCertC`, `botCertT` on the windows (couples)

See `AuxCont` for the statement.  `botCertC_at_jContLevel`: every `J i` of the certified expansion at the gate level `q` is continuous on each side
of `ts 0 = q`.  `botCertC_J_contOn_hi` (window `winCh`), `botCertC_J_contOn_lo` (window `winCl` minus the line `t = L₄ + 1`),
`botCertC_J_contOn_lo_full` (the whole window when the root layer is `≤ L₄` or the index is trivial); the packaged `SepTC`s are
`botCertC_hiTC`, `botCertC_loTC`. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.Links WaveTurbulence.Reg
  WaveTurbulence.LGSpine TTree WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1
  Set WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS5C.P4.Bot

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

include hcan hel htc hcc hup E hN in
theorem botCertC_at_jContLevel (b : BT w ι) (hb : b ∈ canonFinsetK p kind A c0) (q : ℕ)
    (hq : q = zpQ4 A pstar ∨ q = zpQh A pstar)
    (hcoh : IsCoherentCoupleAt p q (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar))
    (i : Fin (botCertC_at (κ := κ) A c0 hA hcan hel htc hcc hup E hN b hb q hq hcoh).m) :
    JContLevel (q : ℝ) ((botCertC_at (κ := κ) A c0 hA hcan hel htc hcc hup E hN b hb q hq hcoh).J i) := by
  unfold botCertC_at
  exact jContLevel_padSel (fun j => ContExp.hJc _ j) i

include hcan hel htc hcc hup E hN in
/-- **The gate level of the certified couple expansion of an index.**  `q` is the level of `botCertC` (`L₄`, a high root's `Lₕ`, or `L₄` for a
trivial index); `q = L₄` unless the index is non-trivial with root layer `> L₄`, in which case `q ≥ L₄ + 1`. -/
theorem botCertC_gate (b : BT w ι) :
    ∃ q : ℕ, q ≤ zpQh A pstar ∧ (q = zpQ4 A pstar ∨ zpQ4 A pstar + 1 ≤ q) ∧
      ((¬ (b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) ∨ cplRootLayer (zpObjC b.1 pstar) ≤ zpQ4 A pstar) →
        q = zpQ4 A pstar) ∧
      ∀ i, JContLevel (q : ℝ) ((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).J i) := by
  classical
  have h4h := zpQ4_le_zpQh A hcan hel htc hcc
  by_cases hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0
  · by_cases hr : cplRootLayer (zpObjC b.1 pstar) ≤ zpQ4 A pstar
    · have e : botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b =
          botCertC_at (κ := κ) A c0 hA hcan hel htc hcc hup E hN b (mem_canon_of_botbs A c0 hb) (zpQ4 A pstar) (Or.inl rfl)
            (botg_coh_lowC A c0 hA hcan hel htc hcc hup hb hr) := by
        unfold botCertC; rw [dif_pos hb, dif_pos hr]
      refine ⟨zpQ4 A pstar, h4h, Or.inl rfl, fun _ => rfl, ?_⟩
      rw [e]
      exact fun i => botCertC_at_jContLevel A c0 hA hcan hel htc hcc hup E hN b _ _ _ _ i
    · have hG := mem_canon_of_botbs A c0 hb
      have hhi := botg_high_C A c0 hA hcan hel htc hcc hup b hG (not_le.1 hr)
      have e : botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b =
          botCertC_at (κ := κ) A c0 hA hcan hel htc hcc hup E hN b hG (zpQQ b.1 pstar).1
            (Or.inr hhi) (botg_nat_cohC A c0 hA hcan hel htc hcc hup b hG) := by
        unfold botCertC; rw [dif_pos hb, dif_neg hr]
      have hc := (botg_cplRoot_le_nat A c0 hA hcan hel htc hcc hup b hG).2
      refine ⟨(zpQQ b.1 pstar).1, hhi.le, Or.inr (by omega), fun h => ?_, ?_⟩
      · rcases h with h | h
        · exact absurd hb h
        · exact absurd h hr
      · rw [e]
        exact fun i => botCertC_at_jContLevel A c0 hA hcan hel htc hcc hup E hN b _ _ _ _ i
  · have e : botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b =
        ObjCert.triv _ (timeBox_subset_cell _ _) (timeBox_subset_closure_interior _ _)
          (timeBox_subset_cell _ _) (timeBox_subset_closure_interior _ _) := by
      unfold botCertC; rw [dif_neg hb]; rfl
    refine ⟨zpQ4 A pstar, h4h, Or.inl rfl, fun _ => rfl, ?_⟩
    rw [e]
    exact fun i => ⟨continuousOn_const, continuousOn_const⟩

include hcan hel htc hcc hup E hN in
/-- **High window**: every certified couple factor is continuous on `winCh`. -/
theorem botCertC_J_contOn_hi (b : BT w ι) (i : Fin (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).m) :
    ContinuousOn ((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).J i) (winCh A pstar) := by
  obtain ⟨q, hqh, -, -, hJ⟩ := botCertC_gate A c0 hA hcan hel htc hcc hup E hN b
  refine (hJ i).mono_ge fun ts hts => ?_
  exact le_trans (by exact_mod_cast hqh) hts.1.1

include hcan hel htc hcc hup E hN in
/-- **Low window** minus the line `t = L₄ + 1`. -/
theorem botCertC_J_contOn_lo (b : BT w ι) (i : Fin (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).m) :
    ContinuousOn ((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).J i)
      (winCl A pstar ∩ {ts | ts 0 < (zpQ4 A pstar : ℝ) + 1}) := by
  obtain ⟨q, -, hq, -, hJ⟩ := botCertC_gate A c0 hA hcan hel htc hcc hup E hN b
  rcases hq with rfl | hq
  · exact (hJ i).mono_ge fun ts hts => hts.1.1.1
  · refine (hJ i).mono_lt fun ts hts => lt_of_lt_of_le hts.2 ?_
    exact_mod_cast hq

include hcan hel htc hcc hup E hN in
/-- **Low window, full**: when the index is trivial or its root layer is `≤ L₄`. -/
theorem botCertC_J_contOn_lo_full (b : BT w ι)
    (hlow : ¬ (b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) ∨ cplRootLayer (zpObjC b.1 pstar) ≤ zpQ4 A pstar)
    (i : Fin (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).m) :
    ContinuousOn ((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).J i) (winCl A pstar) := by
  obtain ⟨q, -, -, hq, hJ⟩ := botCertC_gate A c0 hA hcan hel htc hcc hup E hN b
  rw [hq hlow] at hJ
  exact (hJ i).mono_ge fun ts hts => hts.1.1

include hcan hel htc hcc hup E hN in
/-- The high-window `SepTC` of a certified couple term. -/
noncomputable def botCertC_hiTC (b : BT w ι) (i : Fin (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).m) :
    SepTC P (30 * P.d) (winCh A pstar) (cornH A pstar) (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CJ
      (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CM where
  toSepT := (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).hi i
  Bc := winCh A pstar
  hBcB := subset_rfl
  hBci := ((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).hi i).hint
  hcont := by
    rw [(botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).hi_J i]
    exact botCertC_J_contOn_hi A c0 hA hcan hel htc hcc hup E hN b i

include hcan hel htc hcc hup E hN in
/-- The low-window `SepTC` of a certified couple term (`Bc` = the window minus the line `t = L₄ + 1`). -/
noncomputable def botCertC_loTC (b : BT w ι) (i : Fin (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).m) :
    SepTC P (30 * P.d) (winCl A pstar) (cornL A pstar) (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CJ
      (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CM where
  toSepT := (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo i
  Bc := winCl A pstar ∩ {ts | ts 0 < (zpQ4 A pstar : ℝ) + 1}
  hBcB := inter_subset_left
  hBci := inter_open_closure_interior ((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo i).hint
    (isOpen_lt (continuous_apply 0) continuous_const)
  hcont := by
    rw [(botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo_J i]
    exact botCertC_J_contOn_lo A c0 hA hcan hel htc hcc hup E hN b i

end WaveTurbulence.VineEstS5C.P4.W2
