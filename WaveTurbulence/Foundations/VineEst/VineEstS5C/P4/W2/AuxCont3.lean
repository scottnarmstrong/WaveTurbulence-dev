/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxCont2

/-! # P4-W2 AUX (a'''): continuity of the certified time factors `certC`, `certT` on the windows (trees)

See `AuxCont` for the statement.  `certC_at_jContLevel`: every `J i` of the certified expansion at the gate level `q` is continuous on each side
of `ts 0 = q`.  `certC_J_contOn_hi` (window `winCh`), `certC_J_contOn_lo` (window `winCl` minus the line `t = L₄ + 1`),
`certC_J_contOn_lo_full` (the whole window when the root layer is `≤ L₄` or the index is trivial); the packaged `SepTC`s are
`certC_hiTC`, `certC_loTC`. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.Links WaveTurbulence.Reg
  WaveTurbulence.LGSpine TTree WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1
  Set WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3

set_option linter.unusedSectionVars false

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι]
variable {P : WTParams} {κ : KPar P.d} {Bh : ℕ → ℝ}

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
  (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4)

include hcan hel htc hcc E hN in
theorem certT_at_jContLevel (b : ST w ι pstar J) (hb : b ∈ zpFinset p kind pstar J A sp0 hA) (q : ℕ)
    (hq : q = zpQ4 A pstar ∨ q = zpQh A pstar)
    (hcoh : IsCoherentTreeAt p q (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar))
    (i : Fin (certT_at (κ := κ) A sp0 hA hcan hel htc hcc E hN b hb q hq hcoh).m) :
    JContLevel (q : ℝ) ((certT_at (κ := κ) A sp0 hA hcan hel htc hcc E hN b hb q hq hcoh).J i) := by
  unfold certT_at
  exact jContLevel_padSel (fun j => ContExp.hJc _ j) i

include hcan hel htc hcc E hN in
/-- **The gate level of the certified couple expansion of an index.**  `q` is the level of `certT` (`L₄`, a high root's `Lₕ`, or `L₄` for a
trivial index); `q = L₄` unless the index is non-trivial with root layer `> L₄`, in which case `q ≥ L₄ + 1`. -/
theorem certT_gate (b : ST w ι pstar J) :
    ∃ q : ℕ, q ≤ zpQh A pstar ∧ (q = zpQ4 A pstar ∨ zpQ4 A pstar + 1 ≤ q) ∧
      ((¬ (b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) ∨ treeRootLayer (zpObjT b.1 pstar) ≤ zpQ4 A pstar) →
        q = zpQ4 A pstar) ∧
      ∀ i, JContLevel (q : ℝ) ((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).J i) := by
  classical
  have h4h := zpQ4_le_zpQh A hcan hel htc hcc
  by_cases hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA
  · by_cases hr : treeRootLayer (zpObjT b.1 pstar) ≤ zpQ4 A pstar
    · have e : certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b =
          certT_at (κ := κ) A sp0 hA hcan hel htc hcc E hN b (mem_zpFinset_of_bs A sp0 hA hb) (zpQ4 A pstar) (Or.inl rfl)
            (zp_coh_lowT A sp0 hA hcan hel htc hcc hb hr) := by
        unfold certT; rw [dif_pos hb, dif_pos hr]
      refine ⟨zpQ4 A pstar, h4h, Or.inl rfl, fun _ => rfl, ?_⟩
      rw [e]
      exact fun i => certT_at_jContLevel A sp0 hA hcan hel htc hcc E hN b _ _ _ _ i
    · have hG := mem_zpFinset_of_bs A sp0 hA hb
      have hhi := zp_high_T A sp0 hA hcan hel htc hcc b hG (not_le.1 hr)
      have e : certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b =
          certT_at (κ := κ) A sp0 hA hcan hel htc hcc E hN b hG (zpBranchQ b.1 pstar).1
            (Or.inr hhi) (nat_cohT A sp0 hA hcan hel htc hcc b hG) := by
        unfold certT; rw [dif_pos hb, dif_neg hr]
      have hc := (treeRoot_le_nat A sp0 hA hcan hel htc hcc b hG).2
      refine ⟨(zpBranchQ b.1 pstar).1, hhi.le, Or.inr (by omega), fun h => ?_, ?_⟩
      · rcases h with h | h
        · exact absurd hb h
        · exact absurd h hr
      · rw [e]
        exact fun i => certT_at_jContLevel A sp0 hA hcan hel htc hcc E hN b _ _ _ _ i
  · have e : certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b =
        ObjCert.triv _ (timeBoxGt_subset_cell _ _) (timeBoxGt_subset_closure_interior (L2_le_L4R A hcan hel htc hcc))
          (timeBoxGt_subset_cell _ _) (timeBoxGt_subset_closure_interior (L2_le_LhR A hcan hel htc hcc)) := by
      unfold certT; rw [dif_neg hb]; rfl
    refine ⟨zpQ4 A pstar, h4h, Or.inl rfl, fun _ => rfl, ?_⟩
    rw [e]
    exact fun i => ⟨continuousOn_const, continuousOn_const⟩

include hcan hel htc hcc E hN in
/-- **High window**: every certified couple factor is continuous on `winTh`. -/
theorem certT_J_contOn_hi (b : ST w ι pstar J) (i : Fin (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).m) :
    ContinuousOn ((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).J i) (winTh A pstar) := by
  obtain ⟨q, hqh, -, -, hJ⟩ := certT_gate A sp0 hA hcan hel htc hcc E hN b
  refine (hJ i).mono_ge fun ts hts => ?_
  exact le_trans (by exact_mod_cast hqh) hts.1.1.1

include hcan hel htc hcc E hN in
/-- **Low window** minus the line `t = L₄ + 1`. -/
theorem certT_J_contOn_lo (b : ST w ι pstar J) (i : Fin (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).m) :
    ContinuousOn ((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).J i)
      (winTl A pstar ∩ {ts | ts 0 < (zpQ4 A pstar : ℝ) + 1}) := by
  obtain ⟨q, -, hq, -, hJ⟩ := certT_gate A sp0 hA hcan hel htc hcc E hN b
  rcases hq with rfl | hq
  · exact (hJ i).mono_ge fun ts hts => hts.1.1.1.1
  · refine (hJ i).mono_lt fun ts hts => lt_of_lt_of_le hts.2 ?_
    exact_mod_cast hq

include hcan hel htc hcc E hN in
/-- **Low window, full**: when the index is trivial or its root layer is `≤ L₄`. -/
theorem certT_J_contOn_lo_full (b : ST w ι pstar J)
    (hlow : ¬ (b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) ∨ treeRootLayer (zpObjT b.1 pstar) ≤ zpQ4 A pstar)
    (i : Fin (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).m) :
    ContinuousOn ((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).J i) (winTl A pstar) := by
  obtain ⟨q, -, -, hq, hJ⟩ := certT_gate A sp0 hA hcan hel htc hcc E hN b
  rw [hq hlow] at hJ
  exact (hJ i).mono_ge fun ts hts => hts.1.1.1

include hcan hel htc hcc E hN in
/-- The high-window `SepTC` of a certified couple term. -/
noncomputable def certT_hiTC (b : ST w ι pstar J) (i : Fin (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).m) :
    SepTC P 0 (winTh A pstar) (cornH A pstar) (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CJ
      (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CM where
  toSepT := (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).hi i
  Bc := winTh A pstar
  hBcB := subset_rfl
  hBci := ((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).hi i).hint
  hcont := by
    rw [(certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).hi_J i]
    exact certT_J_contOn_hi A sp0 hA hcan hel htc hcc E hN b i

include hcan hel htc hcc E hN in
/-- The low-window `SepTC` of a certified couple term (`Bc` = the window minus the line `t = L₄ + 1`). -/
noncomputable def certT_loTC (b : ST w ι pstar J) (i : Fin (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).m) :
    SepTC P 0 (winTl A pstar) (cornL A pstar) (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CJ
      (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CM where
  toSepT := (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo i
  Bc := winTl A pstar ∩ {ts | ts 0 < (zpQ4 A pstar : ℝ) + 1}
  hBcB := inter_subset_left
  hBci := inter_open_closure_interior ((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo i).hint
    (isOpen_lt (continuous_apply 0) continuous_const)
  hcont := by
    rw [(certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo_J i]
    exact certT_J_contOn_lo A sp0 hA hcan hel htc hcc E hN b i

end WaveTurbulence.VineEstS5C.P4.W2
