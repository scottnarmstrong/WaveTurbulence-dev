/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5WT.NodeT
public import WaveTurbulence.Foundations.Flower.V5WB.B.Nest
public import WaveTurbulence.Foundations.Flower.V5WB.B.SState

/-! # V5W-T A3 (part 2): the top-weighted member, S-side and nested level sum

The member kernel with the top-weighted weight `bWT` (bond weight of the member's region times `W` at the member's
region top), its S-side `sSumBAtT` (upper block weight `bWT … sb.U sb.a`), and the nested form of the top-weighted
class sum of a level, `classSumBT_nested`, whose lower factor is V5W-B-WORLD's (bond-weighted, no top weight)
`classSumB` of the next level: the top `W` lives on the upper block only.

Copied by source from V5W-B-WORLD `Flower/V5WB/B/SState.lean` (from `sSumBAt`) and `B/Nest.lean` (sha256 in
`COPIED-SHA256SUMS`).  Edits: suffix `T`; the upper weight `bWN ψ κ X sb.U` is `bWT ψ W κ X sb.U sb.a`; its transports
`bWN_false/rigid/twist` are `bWT_false/rigid/twist` (the top is an upper atom `≠ b`, hence not the lower joint of any
operation used); the split of the member weight uses `nodeWeight_glue`; bounds `bWNB … C * CW`.  The lower kernels
(`kTB`, `ktildeB`, `KtilB`, `stIntB`) and `weighted_bundle_sumB` (any bounded upper weight) are V5W-B-WORLD's.
-/

@[expose] public section
noncomputable section
namespace WaveTurbulence.Flower.V5WT
open WaveTurbulence.Flower.V5WB

section Member
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS4 VineEstS5B
variable {w d : ℕ} {ι : Type*}

/-- The top-weighted member kernel of a state at a region. -/
def memberBT (κ : KPar d) (lam : ℝ) (ψ : WD d) (W : (Fin 4 → Mom d) → ℂ) (X : FamilyReconstruction w ι)
    (c : ChainAt X.skeleton X.family) : ℂ :=
  memberMX X.data X.plain (clRegionData X.skeleton c.block c.cl) κ.L κ.γ κ.δ κ.F
    (stateLayer X) (stateLayer_isLayering X) κ.base lam (bWT ψ W κ X c.U c.a) κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h

end Member

section SSide
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS2
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory VineEstS4 VineEstS5B

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι}

/-- The top-weighted S-side of a state at a split (`bWT`: bond weight of the upper block times `W` at its top). -/
@[expose] noncomputable def sSumBAtT (κ : KPar d) (ψ : WD d) (W : (Fin 4 → Mom d) → ℂ)
    (X : FamilyReconstruction w ι) (sp : SplitAt X.skeleton X.family pstar J)
    (Φ : ℝ → Mom d → Mom d → ℂ) : ℂ :=
  sSumW (bWT ψ W κ X sp.sb.U sp.sb.a) sp.RS X.data X.plain κ.L κ.γ κ.δ κ.F (stateLayer X) (stateLayer_isLayering X)
    κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f sp.sb.b.toNode (sp.sb.b.child sp.RS.kept) Φ


section Below
variable (κ : KPar d) (ψ : WD d) (W : (Fin 4 → Mom d) → ℂ) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
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
theorem sSumBAtT_op_false (con : LFConstruction (A.source j hcan hel htc hcc) false) (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSumBAtT κ ψ W (opOut A j hcan hel htc hcc con) (SplitAt.nextA A sp j false) Φ = sSumBAtT κ ψ W A sp Φ := by
  have hU : (SplitAt.nextA A sp j false).sb.U = sp.sb.U := rfl
  unfold sSumBAtT
  rw [show bWT ψ W κ (opOut A j hcan hel htc hcc con) (SplitAt.nextA A sp j false).sb.U
      (SplitAt.nextA A sp j false).sb.a = bWT ψ W κ A sp.sb.U sp.sb.a from
    bWT_false A j hcan hel htc hcc ψ W κ con sp.sb.U sp.sb.a]
  have h := sSumW_false_LF (A.source j hcan hel htc hcc) (bWT ψ W κ A sp.sb.U sp.sb.a) con (SplitAt.lower_notMem_sb A sp hj)
    (SplitAt.nextA A sp j false).RS (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
    (stateLayer (opOut A j hcan hel htc hcc con)) (stateLayer_isLayering (opOut A j hcan hel htc hcc con))
    (stateLayer_spec (opOut A j hcan hel htc hcc con))
    κ.L κ.γ κ.δ κ.F κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f (SplitAt.nextA A sp j false).sb.b.toNode
    ((SplitAt.nextA A sp j false).sb.b.child (SplitAt.nextA A sp j false).RS.kept) Φ
  refine h.trans ?_
  exact sSumW_RS_irrel (bWT ψ W κ A sp.sb.U sp.sb.a) (SplitAt.nextA A sp j false).RS sp.RS A.data A.plain κ.L κ.γ κ.δ κ.F
    (stateLayer A) (stateLayer_isLayering A) κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f sp.sb.b.toNode Φ

/-- **The weighted S-side is invariant under a TRUE operation at a member of `J`.** -/
theorem sSumBAtT_op_true (con : LFConstruction (A.source j hcan hel htc hcc) true) (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSumBAtT κ ψ W (opOut A j hcan hel htc hcc con) (SplitAt.nextA A sp j true) Φ = sSumBAtT κ ψ W A sp Φ := by
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
  unfold sSumBAtT
  change sSumW (bWT ψ W κ (opOut A j hcan hel htc hcc con) (twistedAtoms A.skeleton (A.family.placement j) sp.sb.U)
      (coreBranchEquiv A.skeleton (A.family.placement j) sp.sb.a))
      (SplitAt.nextA A sp j true).RS _ _ κ.L κ.γ κ.δ κ.F _ _ κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f
      (eB (A.family.placement j) sp.sb.b).toNode
      ((eB (A.family.placement j) sp.sb.b).child (SplitAt.nextA A sp j true).RS.kept) Φ = _
  rw [← n0, ← n1]
  exact sSumW_rigid_LF (A.source j hcan hel htc hcc) (bWT ψ W κ A sp.sb.U sp.sb.a) _
    (fun x' => bWT_rigid A j hcan hel htc hcc ψ W κ con hR (Finset.mem_erase.mpr ⟨hS.2.2.2.1, hS.2.1⟩) x') con hS hR sp.RS
    (SplitAt.nextA A sp j true).RS _ _ (stateLayer_spec A) _ _
    (stateLayer_spec (opOut A j hcan hel htc hcc con))
    κ.L κ.γ κ.δ κ.F κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f sp.sb.b.toNode (sp.sb.b.child sp.RS.kept) Φ

omit hj in
/-- **The weighted S-side is invariant under an operation at a member of `J`.** -/
theorem sSumBAtT_op (hj : j ∈ J) (op : FamilyOperation (p := p) (kind := kind) A j) (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSumBAtT κ ψ W op.output (SplitAt.nextA A sp j op.choice) Φ = sSumBAtT κ ψ W A sp Φ := by
  obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
  cases ε
  · exact sSumBAtT_op_false κ ψ W A sp hj hcan hel htc hcc con Φ
  · exact sSumBAtT_op_true κ ψ W A sp hj hcan hel htc hcc con Φ

end Below

theorem sSumBAtT_reachBelow [DecidableEq ι] (hc : Stage1.OpsCommute p kind w ι) (κ : KPar d) (ψ : WD d)
    (W : (Fin 4 → Mom d) → ℂ)
    {A0 : FamilyReconstruction w ι}
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A0 j))
    {M : List ι} {G x : FamilyReconstruction w ι} {sp : SplitAt G.skeleton G.family pstar J}
    {sx : SplitAt x.skeleton x.family pstar J} (h : ReachSp p kind pstar J M G sp x sx) :
    ∀ {Lpre : List ι}, FamilyBatch p kind Lpre A0 G → (Lpre ++ M).Nodup → pstar ∈ Lpre →
      ∀ Φ : ℝ → Mom d → Mom d → ℂ, sSumBAtT κ ψ W x sx Φ = sSumBAtT κ ψ W G sp Φ := by
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
    exact h1.trans (sSumBAtT_op κ ψ W A sp hij op Φ)

/-- The S-side of the skipped state `A`. -/
theorem sSumBAtT_skip (κ : KPar d) (ψ : WD d) (W : (Fin 4 → Mom d) → ℂ) (A : FamilyReconstruction w ι)
    (sp : SplitAt A.skeleton A.family pstar J) (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSumBAtT κ ψ W A sp Φ =
      (coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 sp.RS * clLocalZeta sp.RS *
        ∑' x : ExtS sp.RS κ.L κ.base κ.e κ.f, ∫ σ : CLInternalTime sp.RS,
          bWT ψ W κ A sp.sb.U sp.sb.a x.1 * bundleInt κ A sp Φ false (nuOf A pstar) (rowQ κ A pstar) (rowT κ A pstar) x σ := by
  have hS := SplitAt.slow sp
  unfold sSumBAtT
  rw [sSumW_same A.plain A.data A.data κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) (stateLayer A)
    (stateLayer_isLayering A) κ.base (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained) sp.RS
    κ.t0 κ.t1 κ.t2 κ.e κ.f sp.sb.b.toNode (sp.sb.b.child sp.RS.kept) Φ (bWT ψ W κ A sp.sb.U sp.sb.a) hS.b_mem_erase hS.p0_mem
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (VineEst.SelDataEq.refl _ _ _ _ _ _)]
  congr 1
  refine tsum_congr fun x => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  apply congrArg (bWT ψ W κ A sp.sb.U sp.sb.a x.1 * ·)
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
variable (κ : KPar d) (ψ : WD d) (W : (Fin 4 → Mom d) → ℂ) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
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
theorem sSumBAtT_false (con : LFConstruction (A.source pstar hcan hel htc hcc) false) (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSumBAtT κ ψ W (opOut A pstar hcan hel htc hcc con) (SplitAt.nextA A sp pstar false) Φ =
      (coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 sp.RS * clLocalZeta sp.RS *
        ∑' x : ExtS sp.RS κ.L κ.base κ.e κ.f, ∫ σ : CLInternalTime sp.RS,
          bWT ψ W κ A sp.sb.U sp.sb.a x.1 * bundleInt κ A sp Φ false (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
            (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar)
            x σ := by
  have hS := SplitAt.slow sp
  unfold sSumBAtT
  rw [show bWT ψ W κ (opOut A pstar hcan hel htc hcc con) (SplitAt.nextA A sp pstar false).sb.U
      (SplitAt.nextA A sp pstar false).sb.a = bWT ψ W κ A sp.sb.U sp.sb.a from
    bWT_false A pstar hcan hel htc hcc ψ W κ con sp.sb.U sp.sb.a]
  refine (sSumW_RS_irrel (bWT ψ W κ A sp.sb.U sp.sb.a) (SplitAt.nextA A sp pstar false).RS sp.RS _ _ κ.L κ.γ κ.δ κ.F _ _ κ.base
    κ.t0 κ.t1 κ.t2 κ.e κ.f sp.sb.b.toNode Φ).trans ((sSumW_falseLF (A.source pstar hcan hel htc hcc) con sp.RS hS
    (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A) (stateLayer (opOut A pstar hcan hel htc hcc con))
    (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
    (stateLayer_spec (opOut A pstar hcan hel htc hcc con))
    (bWT ψ W κ A sp.sb.U sp.sb.a) κ.L κ.γ κ.δ κ.F κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f sp.sb.b.toNode (sp.sb.b.child sp.RS.kept) Φ).trans ?_)
  congr 1
  refine tsum_congr fun x => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  exact congrArg (bWT ψ W κ A sp.sb.U sp.sb.a x.1 * ·)
    (sameInt_false_eq κ A sp hcan hel htc hcc con Φ x σ)

/-- **The weighted S-side of a TRUE-choice output (the twisted state) at `p*`, in the chart of `A`.** -/
theorem sSumBAtT_true (con : LFConstruction (A.source pstar hcan hel htc hcc) true) (Φ' : ℝ → Mom d → Mom d → ℂ) :
    sSumBAtT κ ψ W (opOut A pstar hcan hel htc hcc con) (SplitAt.nextA A sp pstar true) Φ' =
      -((coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 sp.RS * clLocalZeta sp.RS *
        ∑' x : ExtS sp.RS κ.L κ.base κ.e κ.f, ∫ σ : CLInternalTime sp.RS,
          bWT ψ W κ A sp.sb.U sp.sb.a x.1 * bundleInt κ A sp (fun t E Fr => Φ' t Fr E) true
            (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
            (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar)
            x σ) := by
  have hT := stw_true A sp
  unfold sSumBAtT
  refine (sSumW_twLF (A.source pstar hcan hel htc hcc) con sp.RS (SplitAt.nextA A sp pstar true).RS hT (stateLayer A)
    (stateLayer_isLayering A) (stateLayer_spec A) (stateLayer (opOut A pstar hcan hel htc hcc con))
    (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
    (stateLayer_spec (opOut A pstar hcan hel htc hcc con))
    (bWT ψ W κ A sp.sb.U sp.sb.a) (bWT ψ W κ (opOut A pstar hcan hel htc hcc con) (SplitAt.nextA A sp pstar true).sb.U
      (SplitAt.nextA A sp pstar true).sb.a)
    (fun x hx => bWT_twist A pstar hcan hel htc hcc ψ W κ con sp.sb.U sp.sb.a
      (fun hl => sp.sb.block.2.2.2.1 (hl.trans (sp.joint.trans sp.bk).symm)) x hx)
    κ.L κ.γ κ.δ κ.F κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f Φ').trans ?_
  congr 2
  refine tsum_congr fun x => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  exact congrArg (bWT ψ W κ A sp.sb.U sp.sb.a x.1 * ·)
    (twInt_true_eq κ A sp hcan hel htc hcc con Φ' x σ)

end Ops

end SSide

section NestT
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback nodeWeight spatialMul addMix addMix_pre engine_mix_bound enginePullback_one freeDict_mul glueAbsConv_spatialMul lkRaw_spatialMul_split rA_glue spatialMul_one termCertW_mul normalized_node_coefficients normalized_node_affine enginePullback_nodeMap)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false memberCoreLayer_eq atom_lowerPC_false atom_lowerPC_true atom_retainedLP mate_lowerPC twistDartEquiv_eq_naive dartNode_naive dartNode_mem_real dartNode_mem_splitA dartNode_mem_support regionDarts_union regionDarts_disjoint enginePullback_mul enginePullback_mono enginePullback_congr enginePullback_finsetProd enginePullback_nodeValue topDarts card_regionDarts_le card_topDarts_le memberCoreLayer regionBondWeight)
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS2
  WaveTurbulence.VineEstS3 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS5C.FlatMod
  TTree MeasureTheory


variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {pstar : ι} {J : Set ι}

theorem memberBT_eq_sSumBAtT (κ : KPar d) (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C)
    (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C) (W : (Fin 4 → Mom d) → ℂ) (CW : ℝ) (hCW : 0 ≤ CW) (hW : ∀ z, ‖W z‖ ≤ CW) (X : FamilyReconstruction w ι) (sp : SplitAt X.skeleton X.family pstar J)
    (hL : κ.L ≠ 0) (hF : HF X.data X.plain κ.L κ.F (stateLayer X) κ.base) :
    memberBT κ lam ψ W X sp.c = sSumBAtT κ ψ W X sp (kTB κ lam ψ X sp) := by
  have hex : sp.RT.excluded = sp.RS.kept := split_excluded_b sp.sb.block sp.hT sp.hi sp.hU sp.RS sp.RT
  have hμ : ∀ p : Σ xS : ExtS sp.RS κ.L κ.base κ.e κ.f,
      CLLocalDecoration sp.RT κ.L κ.base (bdT sp.RT κ.L κ.base xS.1 κ.g κ.h),
      bWT ψ W κ X (sp.sb.U ∪ sp.tb.U) sp.sb.a (glue sp.RS p.1.1 (clExtendIndices sp.RT p.2.1)) =
        bWT ψ W κ X sp.sb.U sp.sb.a p.1.1 * bWN ψ κ X sp.tb.U (clExtendIndices sp.RT p.2.1) := by
    intro p
    unfold bWT
    rw [nodeWeight_glue sp.sb.block sp.hT sp.hi sp.hU sp.RS W κ.L κ.base]
    unfold bWN
    rw [bondWD_union (ΨX ψ X) κ.L κ.base (layX X) sp.sb.block sp.hT sp.hi sp.hU, bondWD_glue_S (ΨX ψ X) κ.L κ.base (layX X) sp.RS,
      bondWD_glue_T (ΨX ψ X) κ.L κ.base (layX X) sp.sb.block sp.hT sp.hi sp.hU sp.RS sp.RT hL p.2.2.2.2]
    ring
  have h1 := memberMX_split_KT_bond sp.sb.block sp.hT sp.hi sp.hU sp.RU sp.RS sp.RT X.data X.plain κ.L κ.γ κ.δ κ.F
    (stateLayer X) (stateLayer_isLayering X) κ.base lam κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h
    (bWT ψ W κ X (sp.sb.U ∪ sp.tb.U) sp.sb.a) (bWT ψ W κ X sp.sb.U sp.sb.a) (bWN ψ κ X sp.tb.U) hL hF hμ
    (bWNB ψ X sp.sb.U C * CW) (bWNB ψ X sp.tb.U C)
    (mul_nonneg (bWNB_nonneg _ _ _ hC) hCW) (bWNB_nonneg _ _ _ hC) (fun x => norm_bWT_le ψ W κ X sp.sb.U sp.sb.a hψ hW x)
    (fun x => norm_bWN_le ψ κ X sp.tb.U C hψ x)
  unfold memberBT
  rw [memberMX_idx sp.union sp.sa.symm sp.tbb.symm (clRegionData X.skeleton sp.c.block sp.c.cl) sp.RU, sp.union, ← sp.sa]
  rw [h1]
  unfold sSumBAtT sSumW kTB
  have hb0 : clBoundaryNodes sp.RT 0 = sp.sb.b.toNode := rfl
  have hb1 : clBoundaryNodes sp.RT 1 = sp.sb.b.child sp.RS.kept := by
    change sp.sb.b.child sp.RT.excluded = _
    rw [hex]
  rw [hb0, hb1]

variable [Fintype ι] [DecidableEq ι]

/-- **(tildeJ2) for an abstract split, weighted.** -/
theorem tildeJ2_BT_of_split (κ : KPar d) (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C)
    (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C) (W : (Fin 4 → Mom d) → ℂ) (CW : ℝ) (hCW : 0 ≤ CW) (hW : ∀ z, ‖W z‖ ≤ CW) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton)
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
    (hL : κ.L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    ∑ x ∈ canonSpFinset p kind pstar J A sp0 hA, memberBT κ lam ψ W x.1 x.2.c =
      ∑ G ∈ zpFinset p kind pstar J A sp0 hA,
        sSumBAtT κ ψ W G.1 G.2 (ktildeB (p := p) (kind := kind) κ lam ψ A sp0 hA G) := by
  classical
  have hc : Stage1.OpsCommute p kind w ι := Stage1.opsCommute_all
  rw [sum_canon hc hA]
  refine Finset.sum_congr rfl fun G hG => ?_
  have hr := (mem_zpFinset hA).mp hG
  have ha : ∀ x ∈ yFinset p kind pstar J A sp0 hA G,
      memberBT κ lam ψ W x.1 x.2.c = sSumBAtT κ ψ W G.1 G.2 (kTB κ lam ψ x.1 x.2) := by
    intro x hx
    obtain ⟨M, hM, hxr⟩ := (mem_yFinset hA hr).mp hx
    rw [memberBT_eq_sSumBAtT κ lam ψ C hC hψ W CW hCW hW x.1 x.2 hL (HF_of_all _ _ _ _ _ _ hF)]
    exact sSumBAtT_reachBelow hc κ ψ W hA0 hxr hr.batch (Lpre := [pstar]) (nodup_pre hM) (List.mem_singleton_self pstar) _
  rw [Finset.sum_congr rfl ha]
  have hsok : ∀ x ∈ yFinset p kind pstar J A sp0 hA G, SOKAt κ G.1 G.2 (kTB κ lam ψ x.1 x.2) := by
    intro x hx
    obtain ⟨M, hM, hxr⟩ := (mem_yFinset hA hr).mp hx
    exact (SOKAt_reachBelow hc κ hA0 hxr hr.batch (Lpre := [pstar]) (nodup_pre hM) (List.mem_singleton_self pstar) _).mp
      (SOKAt_kTB κ lam ψ x.1 x.2 hL (HF_of_all _ _ _ _ _ _ hF) C hC hψ)
  have hlin := sSumW_finsetSum (bWT ψ W κ G.1 G.2.sb.U G.2.sb.a) G.2.RS G.1.data G.1.plain κ.L κ.γ κ.δ κ.F (stateLayer G.1)
    (stateLayer_isLayering G.1) κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f G.2.sb.b.toNode (G.2.sb.b.child G.2.RS.kept)
    (yFinset p kind pstar J A sp0 hA G) (fun x => kTB κ lam ψ x.1 x.2) hsok
    (bWNB ψ G.1 G.2.sb.U C * CW) (mul_nonneg (bWNB_nonneg _ _ _ hC) hCW)
    (fun x => norm_bWT_le ψ W κ G.1 G.2.sb.U G.2.sb.a hψ hW x)
  unfold sSumBAtT at hlin ⊢
  rw [← hlin]
  congr 1
  funext t E F'
  unfold ktildeB
  refine sum_yG_eq_yA hc hA hG (fun x => kTB κ lam ψ x.1 x.2 t E F') (fun y => kTorB κ lam ψ A G.1 pstar y t E F') ?_
  intro x hx y hy hxy
  obtain ⟨M, hM, hxr⟩ := (mem_yFinset hA hr).mp hx
  obtain ⟨My, hMy, hyr⟩ := (mem_yA hA).mp hy
  exact kTB_rel κ lam ψ hA hr hM hMy hxr hyr hxy t E F'

/-- **(tildeJ2) over the canonical representatives, weighted.** -/
theorem tildeJ2_BT_canon (κ : KPar d) (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C)
    (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C) (W : (Fin 4 → Mom d) → ℂ) (CW : ℝ) (hCW : 0 ≤ CW) (hW : ∀ z, ‖W z‖ ≤ CW) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton)
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
    (hL : κ.L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    ∑ y ∈ canonFinsetK p kind A sp0.c, memberBT κ lam ψ W y.1 y.2 =
      ∑ G ∈ zpFinset p kind pstar J A sp0 hA,
        sSumBAtT κ ψ W G.1 G.2 (ktildeB (p := p) (kind := kind) κ lam ψ A sp0 hA G) := by
  rw [← sum_canonSp_eq_canon A sp0 hA (fun y => memberBT κ lam ψ W y.1 y.2)]
  exact tildeJ2_BT_of_split κ lam ψ C hC hψ W CW hCW hW A sp0 hA hA0 hL hF

/-- Each `p*`-state's weighted S-side, in the chart of `A` with `A`'s upper bond weight. -/
theorem zp_stateBWT (κ : KPar d) (lam : ℝ) (ψ : WD d) (W : (Fin 4 → Mom d) → ℂ) (A : FamilyReconstruction w ι)
    (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton)
    {G : ST w ι pstar J} (hG : G ∈ zpFinset p kind pstar J A sp0 hA) :
    sSumBAtT κ ψ W G.1 G.2 (ktildeB (p := p) (kind := kind) κ lam ψ A sp0 hA G) =
      (coupling d κ.L κ.γ κ.δ : ℂ) ^ clLocalOrder1 sp0.RS * clLocalZeta sp0.RS *
        (∑' x : ExtS sp0.RS κ.L κ.base κ.e κ.f, ∫ σ : CLInternalTime sp0.RS,
          bWT ψ W κ A sp0.sb.U sp0.sb.a x.1 * stIntB (p := p) (kind := kind) κ lam ψ A sp0 hA G.1 x σ) := by
  classical
  have hr := (mem_zpFinset hA).mp hG
  obtain ⟨G1, G2⟩ := G
  simp only at hr ⊢
  cases hr with
  | skip _ h =>
    cases h
    have hn : ¬ twAt A A pstar := not_twAt_of_eq rfl
    have e : stIntB (p := p) (kind := kind) κ lam ψ A sp0 hA A =
        bundleInt κ A sp0 (KtilB (p := p) (kind := kind) κ lam ψ A sp0 hA) false (nuOf A pstar)
          (rowQ κ A pstar) (rowT κ A pstar) := by
      funext x σ; simp [stIntB, epsOf, hn]
    rw [e]
    exact sSumBAtT_skip κ ψ W A sp0 _
  | apply op h =>
    cases h
    obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
    cases ε
    · have hn := tw_false A hcan hel htc hcc con
      have hk : ktildeB (p := p) (kind := kind) κ lam ψ A sp0 hA
          ⟨opOut A pstar hcan hel htc hcc con, SplitAt.nextA A sp0 pstar false⟩ =
            KtilB (p := p) (kind := kind) κ lam ψ A sp0 hA := by
        rw [ktildeB_eq]; funext t E F'; simp [hn]
      have e : stIntB (p := p) (kind := kind) κ lam ψ A sp0 hA (opOut A pstar hcan hel htc hcc con) =
          bundleInt κ A sp0 (KtilB (p := p) (kind := kind) κ lam ψ A sp0 hA) false
            (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
            (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar) := by
        funext x σ; simp [stIntB, epsOf, hn]
      rw [hk, e]
      exact sSumBAtT_false κ ψ W A sp0 hcan hel htc hcc con _
    · have ht := tw_true A hcan hel htc hcc con
      have hk : ktildeB (p := p) (kind := kind) κ lam ψ A sp0 hA
          ⟨opOut A pstar hcan hel htc hcc con, SplitAt.nextA A sp0 pstar true⟩ =
          fun t E F' => KtilB (p := p) (kind := kind) κ lam ψ A sp0 hA t F' E := by
        rw [ktildeB_eq]; funext t E F'; simp [ht]
      have e : stIntB (p := p) (kind := kind) κ lam ψ A sp0 hA (opOut A pstar hcan hel htc hcc con) = fun x σ =>
          -bundleInt κ A sp0 (fun t E Fr => (fun t E F' => KtilB (p := p) (kind := kind) κ lam ψ A sp0 hA t F' E) t Fr E)
            true (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
            (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar) x σ := by
        funext x σ; simp [stIntB, epsOf, ht]
      rw [hk, e]
      rw [sSumBAtT_true κ ψ W A sp0 hcan hel htc hcc con]
      simp only [mul_neg, integral_neg, tsum_neg]

section Level
variable {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- **The top-weighted modulated class sum of a level** (members weighted by `bWT`: bond weight times `W` at the
member's region top). -/
noncomputable def classSumBT (lam : ℝ) (ψ : WD d) (W : (Fin 4 → Mom d) → ℂ) (lv : Lvl B) (κ0 : KPar d) (t0 t1 t2 : ℝ)
    (e f g h : Mom d) : ℂ :=
  ∑ z ∈ canonFinsetK p kind (lv.state B RD hG layer hLayer) lv.c,
    memberBT {κ0 with t0 := t0, t1 := t1, t2 := t2, e := e, f := f, g := g, h := h} lam ψ W z.1 z.2

/-- **One level of TARGET Step 4, nested form, with the bond weight.** -/
theorem classSumBT_nested (lam : ℝ) (ψ : WD d) (C : ℝ) (hC : 0 ≤ C)
    (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C) (W : (Fin 4 → Mom d) → ℂ) (CW : ℝ) (hCW : 0 ≤ CW) (hW : ∀ z, ‖W z‖ ≤ CW) (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G) (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (hA0 : ∀ j, j ∉ {j | (lv.e j).1.val < (lv.e pstar).1.val} → j ≠ pstar →
      IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    classSumBT (p := p) (kind := kind) B RD hG layer hLayer lam ψ W lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 (lv.split B RD hG layer hLayer pstar hk).RS *
        clLocalZeta (lv.split B RD hG layer hLayer pstar hk).RS *
        ∑' x : ExtS (lv.split B RD hG layer hLayer pstar hk).RS κ0.L κ0.base e f,
          ∫ σ : CLInternalTime (lv.split B RD hG layer hLayer pstar hk).RS,
            bWT ψ W κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk).sb.U
              (lv.split B RD hG layer hLayer pstar hk).sb.a x.1 *
            (psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk)
              hprime x.1 (clLocalClock (lv.split B RD hG layer hLayer pstar hk).RS ![t0, t1, t2] σ) *
            classSumB (p := p) (kind := kind) B RD hG layer hLayer lam ψ (lv.next B RD hG layer hLayer pstar hk) κ0
              (clLocalClock (lv.split B RD hG layer hLayer pstar hk).RS ![t0, t1, t2] σ
                (lv.split B RD hG layer hLayer pstar hk).sb.b) t1 t2
              (κ0.base + latticePoint κ0.L (x.1 ((lv.state B RD hG layer hLayer).family.placement pstar).lower.toNode))
              (κ0.base + latticePoint κ0.L (x.1 ((lv.state B RD hG layer hLayer).family.placement pstar).retained.toNode))
              g h) := by
  classical
  set A' := lv.state B RD hG layer hLayer with hA'
  set sp := lv.split B RD hG layer hLayer pstar hk with hsp
  let κ : KPar d := { κ0 with t0 := t0, t1 := t1, t2 := t2, e := e, f := f, g := g, h := h }
  have hc : Stage1.OpsCommute p kind w lv.ι := Stage1.opsCommute_all
  have h1 := tildeJ2_BT_canon (p := p) (kind := kind) κ lam ψ C hC hψ W CW hCW hW A' sp hprime hA0 hL hF
  have hKt := KtilB_eq_canon (p := p) (kind := kind) hc
    (Subtype.val : {j : lv.ι // (lv.e j).1.val < (lv.e pstar).1.val} → lv.ι)
    Subtype.val_injective (fun j => j.2) (fun i hi => ⟨⟨i, hi⟩, rfl⟩) κ lam ψ hprime sp hA0
  have e1 : classSumBT (p := p) (kind := kind) B RD hG layer hLayer lam ψ W lv κ0 t0 t1 t2 e f g h =
      ∑ G ∈ zpFinset p kind pstar _ A' sp hprime,
        sSumBAtT κ ψ W G.1 G.2 (ktildeB (p := p) (kind := kind) κ lam ψ A' sp hprime G) := h1
  rw [e1]
  rw [Finset.sum_congr rfl (fun Z hZ => zp_stateBWT κ lam ψ W A' sp hprime hZ), ← Finset.mul_sum,
    weighted_bundle_sumB κ lam ψ C hC hψ A' sp hprime hA0 hL hF (bWT ψ W κ A' sp.sb.U sp.sb.a)
      (bWNB ψ A' sp.sb.U C * CW) (mul_nonneg (bWNB_nonneg _ _ _ hC) hCW)
      (fun x => norm_bWT_le ψ W κ A' sp.sb.U sp.sb.a hψ hW x)]
  congr 1
  refine tsum_congr fun x => integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  beta_reduce
  rw [hKt]
  rfl

end Level

end NestT

end WaveTurbulence.Flower.V5WT
