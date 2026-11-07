/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp3State
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Op1Step

/-! # The S-side is invariant under operations at members below the split (V5 Step 4b, step 4, WP-D)

`sSumAt_op`: for an operation at a member `j ∈ J` (its atoms lie in the lower block `tb`, its lower joint is not the joint `sb.b`),
the S-side `sSumAt κ _ _ Φ` with an arbitrary lower factor `Φ` is the same before and after (rigid twist for `ε = true`, same
skeleton for `ε = false`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS2 WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι}

section Rigid
variable (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J) {j : ι} (hj : j ∈ J)

include hj in
theorem SplitAt.lower_notMem_sb : (A.family.placement j).lower ∉ sp.sb.U := by
  intro h
  have hmem : (A.family.placement j).lower ∈ sp.tb.U := sp.atomsJ j hj (A.family.core j).1.1.2.2.1
  have : (A.family.placement j).lower ∈ sp.sb.U ∩ sp.tb.U := Finset.mem_inter.mpr ⟨h, hmem⟩
  rw [sp.inter] at this
  exact sp.lowJ j hj (Finset.mem_singleton.mp this)

include hj in
theorem SplitAt.rigidAt : RigidAt (A.family.placement j) sp.sb.U sp.sb.b :=
  rigidAt_of_split sp.hT sp.hi sp.clST.2 (A.family.placement j) (A.family.designated j) (sp.atomsJ j hj)
    (A.family.core j).1.1.2.2.1 (by rw [sp.joint]; exact sp.lowJ j hj)

end Rigid

theorem sSum_RS_irrel {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R R' : CLRegionData G S a b)
    (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (t0 t1 t2 : ℝ) (e f : Mom d) (n0 : GNode G.tree)
    (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSum R D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 (b.child R.kept) Φ =
      sSum R' D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 (b.child R'.kept) Φ := by
  rw [regionData_subsingleton R R']

/-- **The S-side is invariant under a FALSE operation at a member of `J`.** -/
theorem sSumAt_op_false (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J) {j : ι}
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
    sSumAt κ (FamilyOperation.output (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A j))
      (SplitAt.nextA A sp j false) Φ = sSumAt κ A sp Φ := by
  have h := sSum_op_false A j hcan hel htc hcc con (SplitAt.lower_notMem_sb A sp hj) (SplitAt.nextA A sp j false).RS
    κ.L κ.γ κ.δ κ.F κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f (SplitAt.nextA A sp j false).sb.b.toNode
    ((SplitAt.nextA A sp j false).sb.b.child (SplitAt.nextA A sp j false).RS.kept) Φ
  unfold sSumAt
  refine h.trans ?_
  exact sSum_RS_irrel (SplitAt.nextA A sp j false).RS sp.RS A.data A.plain κ.L κ.γ κ.δ κ.F (stateLayer A)
    (stateLayer_isLayering A) κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f sp.sb.b.toNode Φ

/-- **The S-side is invariant under a TRUE operation at a member of `J`.** -/
theorem sSumAt_op_true (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J) {j : ι}
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
    sSumAt κ (FamilyOperation.output (⟨hcan, hel, htc, hcc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A j))
      (SplitAt.nextA A sp j true) Φ = sSumAt κ A sp Φ :=
  sSum_op_true A j hcan hel htc hcc con sp.sb.block (SplitAt.rigidAt A sp hj) sp.RS (SplitAt.nextA A sp j true).RS κ.L κ.γ κ.δ κ.F
    κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f Φ

/-- **The S-side is invariant under an operation at a member of `J`.** -/
theorem sSumAt_op (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J) {j : ι} (hj : j ∈ J)
    (op : FamilyOperation (p := p) (kind := kind) A j) (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSumAt κ op.output (SplitAt.nextA A sp j op.choice) Φ = sSumAt κ A sp Φ := by
  obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
  cases ε
  · exact sSumAt_op_false κ A sp hj hcan hel htc hcc con Φ
  · exact sSumAt_op_true κ A sp hj hcan hel htc hcc con Φ

end WaveTurbulence.VineEstS4
