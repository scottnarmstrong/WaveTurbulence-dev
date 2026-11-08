/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.SSum
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.Weight
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp3State
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp4Rigid
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp5Reach
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Cls2Comb
public import WaveTurbulence.Foundations.VineEst.VineEstS5B.StateInt3

/-! # V5-SPACE-EXT: the S-side of a state with its bond weight

`sSumBAt κ ψ X sp Φ`: the S-side at the split `sp` with the bond weight of the upper block. It is invariant under
operations at members below the split (rigid transport of the weight), and for the three choices at `p*` (skip,
FALSE, TRUE) it is the common-chart integrand of `A` with the weight of `A`'s upper block (the TRUE case through the
twist covariance of the bond weight). Adapted from `VineSpaceK.WeightedSOp/SRigid/SReach/SStates`. -/

public section
namespace WaveTurbulence.VineSpaceB
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS2
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory VineEstS4 VineEstS5B

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι}

/-- The weighted S-side of a state at a split. -/
@[expose] noncomputable def sSumBAt (κ : KPar d) (ψ : ℕ → ℕ → Mom d → ℂ)
    (X : FamilyReconstruction w ι) (sp : SplitAt X.skeleton X.family pstar J)
    (Φ : ℝ → Mom d → Mom d → ℂ) : ℂ :=
  sSumW (bW ψ κ X sp.sb.U) sp.RS X.data X.plain κ.L κ.γ κ.δ κ.F (stateLayer X) (stateLayer_isLayering X)
    κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f sp.sb.b.toNode (sp.sb.b.child sp.RS.kept) Φ

theorem sSumW_RS_irrel {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (m : (GNode G.tree → Fin d → ℤ) → ℂ) (R R' : CLRegionData G S a b)
    (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (t0 t1 t2 : ℝ) (e f : Mom d) (n0 : GNode G.tree)
    (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSumW m R D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 (b.child R.kept) Φ =
      sSumW m R' D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 (b.child R'.kept) Φ := by
  rw [regionData_subsingleton R R']

section Below
variable (κ : KPar d) (ψ : ℕ → ℕ → Mom d → ℂ) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
  {j : ι} (hj : j ∈ J) (hcan : CanonicalObject p kind A.layered)
  (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement j) (A.family.kind j)
    (A.family.atoms j) (A.family.upper j))
  (htc : CohOn A.layered ((A.data.tree (A.family.placement j).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement j).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement j).lower.toNode)))
  (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement j).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement j).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement j).retained).secondLeaf A.plain).toNode)))
include hj

/-- **The weighted S-side is invariant under a FALSE operation at a member of `J`.** -/
theorem sSumBAt_op_false (con : LFConstruction (A.source j hcan hel htc hcc) false) (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSumBAt κ ψ (opOut A j hcan hel htc hcc con) (SplitAt.nextA A sp j false) Φ = sSumBAt κ ψ A sp Φ := by
  have hU : (SplitAt.nextA A sp j false).sb.U = sp.sb.U := rfl
  unfold sSumBAt
  rw [show bW ψ κ (opOut A j hcan hel htc hcc con) (SplitAt.nextA A sp j false).sb.U = bW ψ κ A sp.sb.U from
    bW_false A j hcan hel htc hcc ψ κ con sp.sb.U]
  have h := sSumW_false_LF (A.source j hcan hel htc hcc) (bW ψ κ A sp.sb.U) con (SplitAt.lower_notMem_sb A sp hj)
    (SplitAt.nextA A sp j false).RS (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
    (stateLayer (opOut A j hcan hel htc hcc con)) (stateLayer_isLayering (opOut A j hcan hel htc hcc con))
    (stateLayer_spec (opOut A j hcan hel htc hcc con))
    κ.L κ.γ κ.δ κ.F κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f (SplitAt.nextA A sp j false).sb.b.toNode
    ((SplitAt.nextA A sp j false).sb.b.child (SplitAt.nextA A sp j false).RS.kept) Φ
  refine h.trans ?_
  exact sSumW_RS_irrel (bW ψ κ A sp.sb.U) (SplitAt.nextA A sp j false).RS sp.RS A.data A.plain κ.L κ.γ κ.δ κ.F
    (stateLayer A) (stateLayer_isLayering A) κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f sp.sb.b.toNode Φ

/-- **The weighted S-side is invariant under a TRUE operation at a member of `J`.** -/
theorem sSumBAt_op_true (con : LFConstruction (A.source j hcan hel htc hcc) true) (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSumBAt κ ψ (opOut A j hcan hel htc hcc con) (SplitAt.nextA A sp j true) Φ = sSumBAt κ ψ A sp Φ := by
  have hR := SplitAt.rigidAt A sp hj
  have hS := sp.sb.block
  have hk : (SplitAt.nextA A sp j true).RS.kept = sp.RS.kept :=
    kept_eq_rigid (A.family.placement j) hS hR sp.RS (SplitAt.nextA A sp j true).RS
  have n0 : naiveNodeEquiv A.skeleton (A.family.placement j) sp.sb.b.toNode =
      (eB (A.family.placement j) sp.sb.b).toNode := naiveNodeEquiv_branch _ _ sp.sb.b
  have n1 : naiveNodeEquiv A.skeleton (A.family.placement j) (sp.sb.b.child sp.RS.kept) =
      (eB (A.family.placement j) sp.sb.b).child (SplitAt.nextA A sp j true).RS.kept := by
    rw [hk]
    exact hR.child_naive_real hS.2.2.1
      (cl_child_mem_realization_of_internal hS sp.RS hS.2.2.1 sp.RS.kept ((sp.RS.lower sp.RS.kept).mpr rfl))
  unfold sSumBAt
  change sSumW (bW ψ κ (opOut A j hcan hel htc hcc con) (twistedAtoms A.skeleton (A.family.placement j) sp.sb.U))
      (SplitAt.nextA A sp j true).RS _ _ κ.L κ.γ κ.δ κ.F _ _ κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f
      (eB (A.family.placement j) sp.sb.b).toNode
      ((eB (A.family.placement j) sp.sb.b).child (SplitAt.nextA A sp j true).RS.kept) Φ = _
  rw [← n0, ← n1]
  exact sSumW_rigid_LF (A.source j hcan hel htc hcc) (bW ψ κ A sp.sb.U) _
    (fun x' => bW_rigid A j hcan hel htc hcc ψ κ con hR.lower_notMem x') con hS hR sp.RS
    (SplitAt.nextA A sp j true).RS _ _ (stateLayer_spec A) _ _
    (stateLayer_spec (opOut A j hcan hel htc hcc con))
    κ.L κ.γ κ.δ κ.F κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f sp.sb.b.toNode (sp.sb.b.child sp.RS.kept) Φ

omit hj in
/-- **The weighted S-side is invariant under an operation at a member of `J`.** -/
theorem sSumBAt_op (hj : j ∈ J) (op : FamilyOperation (p := p) (kind := kind) A j) (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSumBAt κ ψ op.output (SplitAt.nextA A sp j op.choice) Φ = sSumBAt κ ψ A sp Φ := by
  obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
  cases ε
  · exact sSumBAt_op_false κ ψ A sp hj hcan hel htc hcc con Φ
  · exact sSumBAt_op_true κ ψ A sp hj hcan hel htc hcc con Φ

end Below

theorem sSumBAt_reachBelow [DecidableEq ι] (hc : Stage1.OpsCommute p kind w ι) (κ : KPar d) (ψ : ℕ → ℕ → Mom d → ℂ)
    {A0 : FamilyReconstruction w ι}
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A0 j))
    {M : List ι} {G x : FamilyReconstruction w ι} {sp : SplitAt G.skeleton G.family pstar J}
    {sx : SplitAt x.skeleton x.family pstar J} (h : ReachSp p kind pstar J M G sp x sx) :
    ∀ {Lpre : List ι}, FamilyBatch p kind Lpre A0 G → (Lpre ++ M).Nodup → pstar ∈ Lpre →
      ∀ Φ : ℝ → Mom d → Mom d → ℂ, sSumBAt κ ψ x sx Φ = sSumBAt κ ψ G sp Φ := by
  induction h with
  | nil A sp => intros; rfl
  | skip i h ih =>
    intro Lpre hpre hnd hp Φ
    exact ih hpre (hnd.sublist (List.Sublist.append_left (List.sublist_cons_self _ _) _)) hp Φ
  | @apply L A sp B sp' i op h ih =>
    intro Lpre hpre hnd hp Φ
    have hnd' : (Lpre ++ i :: L).Nodup := hnd
    have hiL : i ∉ Lpre := fun hi => by
      have := List.nodup_append.mp hnd'
      exact this.2.2 i hi i List.mem_cons_self rfl
    have hij : i ∈ J := by
      by_contra hnJ
      have hne : i ≠ pstar := fun e => hiL (e ▸ hp)
      exact (noop_batch hc hpre hiL (hA0 i hnJ hne)).false op
    have h1 := ih (Lpre := Lpre ++ [i]) (Stage1.familyBatch_append hpre (.apply op (.nil _)))
      (by simpa using hnd') (List.mem_append_left _ hp) Φ
    exact h1.trans (sSumBAt_op κ ψ A sp hij op Φ)

/-- The S-side of the skipped state `A`. -/
theorem sSumBAt_skip (κ : KPar d) (ψ : ℕ → ℕ → Mom d → ℂ) (A : FamilyReconstruction w ι)
    (sp : SplitAt A.skeleton A.family pstar J) (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSumBAt κ ψ A sp Φ =
      (coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 sp.RS * clLocalZeta sp.RS *
        ∑' x : ExtS sp.RS κ.L κ.base κ.e κ.f, ∫ σ : CLInternalTime sp.RS,
          bW ψ κ A sp.sb.U x.1 * bundleInt κ A sp Φ false (nuOf A pstar) (rowQ κ A pstar) (rowT κ A pstar) x σ := by
  have hS := SplitAt.slow sp
  unfold sSumBAt
  rw [sSumW_same A.plain A.data A.data κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) (stateLayer A)
    (stateLayer_isLayering A) κ.base (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) sp.RS
    κ.t0 κ.t1 κ.t2 κ.e κ.f sp.sb.b.toNode (sp.sb.b.child sp.RS.kept) Φ (bW ψ κ A sp.sb.U) hS.b_mem_erase hS.p0_mem
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (VineEst.SelDataEq.refl _ _ _ _ _ _)]
  congr 1
  refine tsum_congr fun x => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  apply congrArg (bW ψ κ A sp.sb.U x.1 * ·)
  have hn0 : sp.sb.b.toNode = (A.family.placement pstar).lower.toNode := congrArg GBranch.toNode hS.lower
  have hn1 : sp.sb.b.child sp.RS.kept = (A.family.placement pstar).retained.toNode := by
    rw [hS.keep, hS.lower]
    exact (A.family.placement pstar).child.symm
  have hex := exc_same (A.family.placement pstar) A.plain A.data κ.L κ.γ κ.δ κ.F (stateLayer A)
    (stateLayer_isLayering A) κ.base (S := sp.sb.U) (a := sp.sb.a) hS.lower x.1 (hS.pairedAt_ext x)
    (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ)
  have hT : VineEst.selTreeRow κ.L κ.γ κ.δ κ.F A.data A.plain (stateLayer A) (stateLayer_isLayering A) sp.sb.b =
      VineEst.selTreeRow κ.L κ.γ κ.δ κ.F A.data A.plain (stateLayer A) (stateLayer_isLayering A)
        (A.family.placement pstar).lower := by
    rw [hS.lower]
  unfold sameInt bundleInt
  rw [hex, hn0, hn1, hT]
  rfl

section Ops
variable (κ : KPar d) (ψ : ℕ → ℕ → Mom d → ℂ) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
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

/-- **The weighted S-side of a FALSE-choice output at `p*`, in the chart of `A`.** -/
theorem sSumBAt_false (con : LFConstruction (A.source pstar hcan hel htc hcc) false) (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSumBAt κ ψ (opOut A pstar hcan hel htc hcc con) (SplitAt.nextA A sp pstar false) Φ =
      (coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 sp.RS * clLocalZeta sp.RS *
        ∑' x : ExtS sp.RS κ.L κ.base κ.e κ.f, ∫ σ : CLInternalTime sp.RS,
          bW ψ κ A sp.sb.U x.1 * bundleInt κ A sp Φ false (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
            (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar)
            x σ := by
  have hS := SplitAt.slow sp
  unfold sSumBAt
  rw [show bW ψ κ (opOut A pstar hcan hel htc hcc con) (SplitAt.nextA A sp pstar false).sb.U = bW ψ κ A sp.sb.U from
    bW_false A pstar hcan hel htc hcc ψ κ con sp.sb.U]
  refine (sSumW_RS_irrel (bW ψ κ A sp.sb.U) (SplitAt.nextA A sp pstar false).RS sp.RS _ _ κ.L κ.γ κ.δ κ.F _ _ κ.base
    κ.t0 κ.t1 κ.t2 κ.e κ.f sp.sb.b.toNode Φ).trans ((sSumW_falseLF (A.source pstar hcan hel htc hcc) con sp.RS hS
    (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A) (stateLayer (opOut A pstar hcan hel htc hcc con))
    (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
    (stateLayer_spec (opOut A pstar hcan hel htc hcc con))
    (bW ψ κ A sp.sb.U) κ.L κ.γ κ.δ κ.F κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f sp.sb.b.toNode (sp.sb.b.child sp.RS.kept) Φ).trans ?_)
  congr 1
  refine tsum_congr fun x => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  exact congrArg (bW ψ κ A sp.sb.U x.1 * ·)
    (sameInt_false_eq κ A sp hcan hel htc hcc con Φ x σ)

/-- **The weighted S-side of a TRUE-choice output (the twisted state) at `p*`, in the chart of `A`.** -/
theorem sSumBAt_true (con : LFConstruction (A.source pstar hcan hel htc hcc) true) (Φ' : ℝ → Mom d → Mom d → ℂ) :
    sSumBAt κ ψ (opOut A pstar hcan hel htc hcc con) (SplitAt.nextA A sp pstar true) Φ' =
      -((coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 sp.RS * clLocalZeta sp.RS *
        ∑' x : ExtS sp.RS κ.L κ.base κ.e κ.f, ∫ σ : CLInternalTime sp.RS,
          bW ψ κ A sp.sb.U x.1 * bundleInt κ A sp (fun t E Fr => Φ' t Fr E) true
            (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
            (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar)
            x σ) := by
  have hT := stw_true A sp
  unfold sSumBAt
  refine (sSumW_twLF (A.source pstar hcan hel htc hcc) con sp.RS (SplitAt.nextA A sp pstar true).RS hT (stateLayer A)
    (stateLayer_isLayering A) (stateLayer_spec A) (stateLayer (opOut A pstar hcan hel htc hcc con))
    (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
    (stateLayer_spec (opOut A pstar hcan hel htc hcc con))
    (bW ψ κ A sp.sb.U) (bW ψ κ (opOut A pstar hcan hel htc hcc con) (SplitAt.nextA A sp pstar true).sb.U)
    (fun x hx => bW_twist A pstar hcan hel htc hcc ψ κ con sp.sb.U x hx)
    κ.L κ.γ κ.δ κ.F κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f Φ').trans ?_
  congr 2
  refine tsum_congr fun x => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  exact congrArg (bW ψ κ A sp.sb.U x.1 * ·)
    (twInt_true_eq κ A sp hcan hel htc hcc con Φ' x σ)

end Ops

end WaveTurbulence.VineSpaceB
