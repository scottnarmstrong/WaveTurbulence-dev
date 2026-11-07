/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B.StateInt2

/-! # V5 Step 4d-B: the S-side of the states of `Zp(A)` in the chart of `A` (part 3: outputs of an operation at `p*`)

`sSumAt_false`: FALSE choice (same skeleton).  `sSumAt_true`: TRUE choice, the twisted state: the sign `-1`, the lower factor read
at the exchanged labels, the clocks of the parents of the lower joint and of the partner exchanged (`bundleInt ... true`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} {d : ℕ}

section Ops
variable (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
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

theorem sigStar_false (con : LFConstruction (A.source pstar hcan hel htc hcc) false) :
    sigStar (opOut A pstar hcan hel htc hcc con) pstar =
      (A.skeleton.sign (A.family.placement pstar).lower.toNode,
        nativeCoupleLayered con.data A.plain (stateLayer (opOut A pstar hcan hel htc hcc con))
          (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
          (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained),
        nativeChainLayered con.data A.plain (stateLayer (opOut A pstar hcan hel htc hcc con))
          (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) (A.family.placement pstar).lower) := by
  have h := sigStar_output A pstar hcan hel htc hcc con
  have hq : chosenPairEquiv A.skeleton (A.family.placement pstar) A.plain false
      (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) =
      pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained :=
    pairOfLeaf_firstLeaf A.skeleton A.plain _
  rw [hq] at h
  exact h

theorem sigStar_true (con : LFConstruction (A.source pstar hcan hel htc hcc) true) :
    sigStar (opOut A pstar hcan hel htc hcc con) pstar =
      ((unitTwistGarden A.skeleton (A.family.placement pstar)).sign (eB (A.family.placement pstar) (A.family.placement pstar).lower).toNode,
        nativeCoupleLayered con.data (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain)
          (stateLayer (opOut A pstar hcan hel htc hcc con))
          (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
          (tp (A.family.placement pstar) A.plain (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)),
        nativeChainLayered con.data (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain)
          (stateLayer (opOut A pstar hcan hel htc hcc con))
          (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
          (eB (A.family.placement pstar) (A.family.placement pstar).lower)) :=
  sigStar_output A pstar hcan hel htc hcc con

theorem sameInt_false_eq (con : LFConstruction (A.source pstar hcan hel htc hcc) false)
    (Φ : ℝ → Mom d → Mom d → ℂ) (x : ExtS sp.RS κ.L κ.base κ.e κ.f) (σ : CLInternalTime sp.RS) :
    sameInt A.plain A.data con.data κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        κ.base (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) sp.RS κ.t0 κ.t1 κ.t2 κ.e κ.f
        sp.sb.b.toNode (sp.sb.b.child sp.RS.kept) Φ x σ =
      bundleInt κ A sp Φ false (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
        (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar) x σ := by
  have hS := SplitAt.slow sp
  have hn0 : sp.sb.b.toNode = (A.family.placement pstar).lower.toNode := congrArg GBranch.toNode hS.lower
  have hn1 : sp.sb.b.child sp.RS.kept = (A.family.placement pstar).retained.toNode := by
    rw [hS.keep, hS.lower]
    exact (A.family.placement pstar).child.symm
  have hex := exc_same (A.family.placement pstar) A.plain con.data κ.L κ.γ κ.δ κ.F
    (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
    κ.base (S := sp.sb.U) (a := sp.sb.a) hS.lower x.1 (hS.pairedAt_ext x) (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ)
  have hT : VineEst.selTreeRow κ.L κ.γ κ.δ κ.F con.data A.plain (stateLayer (opOut A pstar hcan hel htc hcc con))
      (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) sp.sb.b =
      VineEst.selTreeRow κ.L κ.γ κ.δ κ.F con.data A.plain (stateLayer (opOut A pstar hcan hel htc hcc con))
      (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) (A.family.placement pstar).lower := by
    rw [hS.lower]
  unfold sameInt bundleInt
  unfold nuOf rowQ rowT
  show spartFrame A.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base sp.sb.U sp.sb.a sp.sb.b
      (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) x.1 (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ) *
    (spartExc con.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer (opOut A pstar hcan hel htc hcc con))
      (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base sp.sb.U sp.sb.a sp.sb.b
      (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) x.1 (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ) *
      Φ (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ sp.sb.b) (κ.base + latticePoint κ.L (x.1 sp.sb.b.toNode))
        (κ.base + latticePoint κ.L (x.1 (sp.sb.b.child sp.RS.kept)))) = _
  rw [sigStar_false A hcan hel htc hcc con]
  erw [hex]
  rw [hn0, hn1]
  erw [hT]
  rfl

/-- **The S-side of a FALSE-choice output at `p*`, in the chart of `A`.** -/
theorem sSumAt_false (con : LFConstruction (A.source pstar hcan hel htc hcc) false) (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSumAt κ (opOut A pstar hcan hel htc hcc con) (SplitAt.nextA A sp pstar false) Φ =
      (coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 sp.RS * clLocalZeta sp.RS *
        ∑' x : ExtS sp.RS κ.L κ.base κ.e κ.f, ∫ σ : CLInternalTime sp.RS,
          bundleInt κ A sp Φ false (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
            (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar)
            x σ := by
  have hS := SplitAt.slow sp
  unfold sSumAt
  refine (sSum_RS_irrel (SplitAt.nextA A sp pstar false).RS sp.RS _ _ κ.L κ.γ κ.δ κ.F _ _ κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f
    sp.sb.b.toNode Φ).trans ((sSum_falseLF (A.source pstar hcan hel htc hcc) con sp.RS hS (stateLayer A)
    (stateLayer_isLayering A) (stateLayer_spec A) (stateLayer (opOut A pstar hcan hel htc hcc con))
    (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
    (stateLayer_spec (opOut A pstar hcan hel htc hcc con))
    κ.L κ.γ κ.δ κ.F κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f sp.sb.b.toNode (sp.sb.b.child sp.RS.kept) Φ).trans ?_)
  congr 1
  refine tsum_congr fun x => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  exact sameInt_false_eq κ A sp hcan hel htc hcc con Φ x σ
/-- The pair of the retained leaf of the twisted state is the twist image of the source pair. -/
theorem retainedPair_true (con : LFConstruction (A.source pstar hcan hel htc hcc) true) :
    pairOfLeaf (opOut A pstar hcan hel htc hcc con).skeleton (opOut A pstar hcan hel htc hcc con).plain
        ((opOut A pstar hcan hel htc hcc con).family.placement pstar).retained =
      tp (A.family.placement pstar) A.plain (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) := by
  have hr : (A.family.nextPlacement pstar pstar).retained =
      coreLeafEquiv A.skeleton (A.family.placement pstar) (A.family.placement pstar).retained :=
    A.family.nextPlacement_retained pstar pstar
  have hq : chosenPairEquiv A.skeleton (A.family.placement pstar) A.plain true
      (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) =
      pairOfLeaf (unitTwistGarden A.skeleton (A.family.placement pstar)) (unitTwistGarden_plain _ _ A.plain)
        (coreLeafEquiv A.skeleton (A.family.placement pstar) (A.family.placement pstar).retained) :=
    sourcePairEquiv_pairOfLeaf A.plain (unitTwistGarden_plain _ _ A.plain)
      (coreLeafEquiv A.skeleton (A.family.placement pstar)) (fun l => (unitTwistGarden_pair _ _ l).symm) _
  show pairOfLeaf (unitTwistGarden A.skeleton (A.family.placement pstar)) _ (A.family.nextPlacement pstar pstar).retained = _
  rw [hr, ← hq]
  rfl

/-- **The selected exceptional couple row of the twisted state** is the selected row of the twist image of the source
pair (ruling F2; the selection data are read at the same pair). -/
theorem rowQ_true_eq (con : LFConstruction (A.source pstar hcan hel htc hcc) true) :
    rowQ κ (opOut A pstar hcan hel htc hcc con) pstar =
      VineEst.selCoupleRow κ.L κ.γ κ.δ κ.F con.data (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (tp (A.family.placement pstar) A.plain (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)) := by
  unfold rowQ sigStar
  rw [retainedPair_true A hcan hel htc hcc con]
  rfl

/-- **The selected exceptional tree row of the twisted state** is the selected row at the twist image of the lower
joint. -/
theorem rowT_true_eq (con : LFConstruction (A.source pstar hcan hel htc hcc) true) :
    rowT κ (opOut A pstar hcan hel htc hcc con) pstar =
      VineEst.selTreeRow κ.L κ.γ κ.δ κ.F con.data (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (eB (A.family.placement pstar) (A.family.placement pstar).lower) := by
  have hl : ((opOut A pstar hcan hel htc hcc con).family.placement pstar).lower =
      eB (A.family.placement pstar) (A.family.placement pstar).lower :=
    A.family.nextPlacement_lower pstar pstar
  unfold rowT sigStar
  rw [hl]
  rfl

theorem twInt_true_eq (con : LFConstruction (A.source pstar hcan hel htc hcc) true) (Φ' : ℝ → Mom d → Mom d → ℂ)
    (x : ExtS sp.RS κ.L κ.base κ.e κ.f) (σ : CLInternalTime sp.RS) :
    twInt (RS' := (SplitAt.nextA A sp pstar true).RS) A.plain A.data con.data κ.L κ.γ κ.δ κ.F (stateLayer A)
        (stateLayer_isLayering A) (stateLayer (opOut A pstar hcan hel htc hcc con))
        (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f Φ' x σ =
      bundleInt κ A sp (fun t E Fr => Φ' t Fr E) true (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
        (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar) x σ := by
  have hS := SplitAt.slow sp
  have hu : ∀ v ∈ sp.sb.U, clLocalClock (SplitAt.nextA A sp pstar true).RS ![κ.t0, κ.t1, κ.t2]
      (tEquivS (A.family.placement pstar) sp.RS (SplitAt.nextA A sp pstar true).RS σ) (eB (A.family.placement pstar) v) =
      clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ v :=
    fun v hv => clockS_corr (A.family.placement pstar) sp.RS (SplitAt.nextA A sp pstar true).RS _ σ hv
  have hex := exc_tw (A.family.placement pstar) A.plain con.data κ.L κ.γ κ.δ κ.F
    (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
    κ.base sp.sb.U (a := sp.sb.a) hS.lower x.1
    (clLocalClock (SplitAt.nextA A sp pstar true).RS ![κ.t0, κ.t1, κ.t2]
      (tEquivS (A.family.placement pstar) sp.RS (SplitAt.nextA A sp pstar true).RS σ))
    (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ) (hu _ hS.block.2.2.1) (hu _ hS.qb_mem) (hu _ hS.qr_mem)
  have hb : eB (A.family.placement pstar) sp.sb.b = eB (A.family.placement pstar) (A.family.placement pstar).lower := by
    rw [hS.lower]
  unfold twInt bundleInt
  rw [rowQ_true_eq κ A hcan hel htc hcc con, rowT_true_eq κ A hcan hel htc hcc con]
  unfold nuOf
  rw [sigStar_true A hcan hel htc hcc con]
  erw [hex]
  rw [hb]
  rfl

/-- **The S-side of a TRUE-choice output (the twisted state) at `p*`, in the chart of `A`.** -/
theorem sSumAt_true (con : LFConstruction (A.source pstar hcan hel htc hcc) true) (Φ' : ℝ → Mom d → Mom d → ℂ) :
    sSumAt κ (opOut A pstar hcan hel htc hcc con) (SplitAt.nextA A sp pstar true) Φ' =
      -((coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 sp.RS * clLocalZeta sp.RS *
        ∑' x : ExtS sp.RS κ.L κ.base κ.e κ.f, ∫ σ : CLInternalTime sp.RS,
          bundleInt κ A sp (fun t E Fr => Φ' t Fr E) true (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
            (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar)
            x σ) := by
  have hS := SplitAt.slow sp
  have hT := stw_true A sp
  unfold sSumAt
  refine (sSum_twLF (A.source pstar hcan hel htc hcc) con sp.RS (SplitAt.nextA A sp pstar true).RS hT (stateLayer A)
    (stateLayer_isLayering A) (stateLayer_spec A) (stateLayer (opOut A pstar hcan hel htc hcc con))
    (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
    (stateLayer_spec (opOut A pstar hcan hel htc hcc con))
    κ.L κ.γ κ.δ κ.F κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f Φ').trans ?_
  congr 2
  refine tsum_congr fun x => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  exact twInt_true_eq κ A sp hcan hel htc hcc con Φ' x σ

end Ops

end WaveTurbulence.VineEstS5B
