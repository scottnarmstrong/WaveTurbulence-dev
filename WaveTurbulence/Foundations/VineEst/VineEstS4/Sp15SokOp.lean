/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp14Op
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp5Reach

/-! # `SOKAt` along operations at members of `J` and along batches (V5 Step 4b, step 4, WP-E, part 5) -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS2 WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι}

theorem SOK_RS_irrel {w d : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (R R' : CLRegionData G S a b) (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (t0 t1 t2 : ℝ)
    (e f : Mom d) (n0 : GNode G.tree) (Φ : ℝ → Mom d → Mom d → ℂ) :
    SOK R D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 (b.child R.kept) Φ ↔
      SOK R' D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 (b.child R'.kept) Φ := by
  rw [regionData_subsingleton R R']

theorem SOK_nodes_congr {w d : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (R : CLRegionData G S a b) (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (t0 t1 t2 : ℝ)
    (e f : Mom d) {n0 n0' n1 n1' : GNode G.tree} (h0 : n0 = n0') (h1 : n1 = n1') (Φ : ℝ → Mom d → Mom d → ℂ) :
    SOK R D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 Φ ↔
      SOK R D hG L γ δ F layer hLayer base t0 t1 t2 e f n0' n1' Φ := by
  subst h0 h1; rfl

theorem SOKAt_op_false (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J) {j : ι}
    (hj : j ∈ J) (hcan : CanonicalObject p kind A.layered)
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
    (con : LFConstruction (A.source j hcan hel htc hcc) false) (Φ : ℝ → Mom d → Mom d → ℂ) :
    SOKAt κ (FamilyOperation.output (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A j))
      (SplitAt.nextA A sp j false) Φ ↔ SOKAt κ A sp Φ := by
  have h := SOK_false_LF_iff (A.source j hcan hel htc hcc) con (SplitAt.lower_notMem_sb A sp hj)
    (SplitAt.nextA A sp j false).RS _ _ (stateLayer_spec A) _ _
    (stateLayer_spec (FamilyOperation.output (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A j)))
    κ.L κ.γ κ.δ κ.F κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f (SplitAt.nextA A sp j false).sb.b.toNode
    ((SplitAt.nextA A sp j false).sb.b.child (SplitAt.nextA A sp j false).RS.kept) Φ
  unfold SOKAt
  refine h.trans ?_
  exact SOK_RS_irrel (SplitAt.nextA A sp j false).RS sp.RS A.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer A)
    (stateLayer_isLayering A) κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f sp.sb.b.toNode Φ

theorem SOKAt_op_true (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J) {j : ι}
    (hj : j ∈ J) (hcan : CanonicalObject p kind A.layered)
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
    (con : LFConstruction (A.source j hcan hel htc hcc) true) (Φ : ℝ → Mom d → Mom d → ℂ) :
    SOKAt κ (FamilyOperation.output (⟨hcan, hel, htc, hcc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A j))
      (SplitAt.nextA A sp j true) Φ ↔ SOKAt κ A sp Φ := by
  have hR := SplitAt.rigidAt A sp hj
  have hk : (SplitAt.nextA A sp j true).RS.kept = sp.RS.kept :=
    kept_eq_rigid (A.family.placement j) sp.sb.block hR sp.RS (SplitAt.nextA A sp j true).RS
  have n0 : naiveNodeEquiv A.skeleton (A.family.placement j) sp.sb.b.toNode =
      (eB (A.family.placement j) sp.sb.b).toNode := naiveNodeEquiv_branch _ _ sp.sb.b
  have n1 : naiveNodeEquiv A.skeleton (A.family.placement j) (sp.sb.b.child sp.RS.kept) =
      (eB (A.family.placement j) sp.sb.b).child (SplitAt.nextA A sp j true).RS.kept := by
    rw [hk]
    exact hR.child_naive_real sp.sb.block.2.2.1
      (cl_child_mem_realization_of_internal sp.sb.block sp.RS sp.sb.block.2.2.1 sp.RS.kept ((sp.RS.lower sp.RS.kept).mpr rfl))
  have h := SOK_rigid_LF_iff (A.source j hcan hel htc hcc) con sp.sb.block hR sp.RS (SplitAt.nextA A sp j true).RS _ _
    (stateLayer_spec A) _ _
    (stateLayer_spec (FamilyOperation.output (⟨hcan, hel, htc, hcc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A j)))
    κ.L κ.γ κ.δ κ.F κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f sp.sb.b.toNode (sp.sb.b.child sp.RS.kept) Φ
  have e0 : (SplitAt.nextA A sp j true).sb.b.toNode =
      naiveNodeEquiv A.skeleton (A.family.placement j) sp.sb.b.toNode := n0.symm
  have e1 : (SplitAt.nextA A sp j true).sb.b.child (SplitAt.nextA A sp j true).RS.kept =
      naiveNodeEquiv A.skeleton (A.family.placement j) (sp.sb.b.child sp.RS.kept) := n1.symm
  unfold SOKAt
  exact Iff.trans (SOK_nodes_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e0 e1 _) h

theorem SOKAt_op (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J) {j : ι} (hj : j ∈ J)
    (op : FamilyOperation (p := p) (kind := kind) A j) (Φ : ℝ → Mom d → Mom d → ℂ) :
    SOKAt κ op.output (SplitAt.nextA A sp j op.choice) Φ ↔ SOKAt κ A sp Φ := by
  obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
  cases ε
  · exact SOKAt_op_false κ A sp hj hcan hel htc hcc con Φ
  · exact SOKAt_op_true κ A sp hj hcan hel htc hcc con Φ

theorem SOKAt_reachBelow [DecidableEq ι] (hc : Stage1.OpsCommute p kind w ι) (κ : KPar d) {A0 : FamilyReconstruction w ι}
    (hA0 : ∀ j, j ∉ J → j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A0 j))
    {M : List ι} {G x : FamilyReconstruction w ι} {sp : SplitAt G.skeleton G.family pstar J}
    {sx : SplitAt x.skeleton x.family pstar J} (h : ReachSp p kind pstar J M G sp x sx) :
    ∀ {Lpre : List ι}, FamilyBatch p kind Lpre A0 G → (Lpre ++ M).Nodup → pstar ∈ Lpre →
      ∀ Φ : ℝ → Mom d → Mom d → ℂ, SOKAt κ x sx Φ ↔ SOKAt κ G sp Φ := by
  induction h with
  | nil A sp => intros; exact Iff.rfl
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
    exact h1.trans (SOKAt_op κ A sp hij op Φ)

end WaveTurbulence.VineEstS4
