/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp5Reach

/-! # The lower kernel under the operation at `pstar` (V5 Step 4b, step 4, WP-D)

`kT_op_true` / `kT_op_false`: after the operation at the member `pstar` itself (whose lower joint is the upper joint of the lower
block `tb`), `kT` is the kernel of the source with the first two boundary momenta exchanged (TRUE) or unchanged (FALSE)
(`kernelT_op_true/false`, `clLocalKernel_twist_LF`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS2 WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*} {d : ℕ} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι}

theorem kernelT_op_true' {A : FamilyReconstruction w ι} {i : ι} {hcan : CanonicalObject p kind A.layered}
    {hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement i) (A.family.kind i)
      (A.family.atoms i) (A.family.upper i)}
    {htc : CohOn A.layered ((A.data.tree (A.family.placement i).lower).linksAt
      (nodeSign A.skeleton.sig (A.family.placement i).lower.1)
      (inflatedPosition A.skeleton A.data.tree (A.family.placement i).lower.toNode))}
    {hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)).linksAt
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).firstLeaf A.plain).toNode)
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).secondLeaf A.plain).toNode))}
    (con : LFConstruction (A.source i hcan hel htc hcc) true)
    {T : Finset (GBranch A.skeleton.tree)} {b z : GBranch A.skeleton.tree} (hb : b = (A.family.placement i).lower)
    (hB : A.skeleton.molecule.IsBlock T b z) (hCL : Mole.CLParentPattern A.skeleton T b z)
    (R : CLRegionData A.skeleton T b z)
    (R' : CLRegionData (unitTwistGarden A.skeleton (A.family.placement i)) (twistedAtoms A.skeleton (A.family.placement i) T)
      (coreBranchEquiv A.skeleton (A.family.placement i) b) (coreBranchEquiv A.skeleton (A.family.placement i) z))
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f g k : Mom d) :
    clLocalKernel (FamilyOperation.output (⟨hcan, hel, htc, hcc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i)).data
        (FamilyOperation.output (⟨hcan, hel, htc, hcc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i)).plain
        R' L γ δ F (stateLayer (FamilyOperation.output
          (⟨hcan, hel, htc, hcc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i)))
        (stateLayer_isLayering _) base t0 t1 t2 e f g k =
      clLocalKernel A.data A.plain R L γ δ F (stateLayer A) (stateLayer_isLayering A) base t0 t1 t2 f e g k := by
  subst hb
  exact kernelT_op_true A i hcan hel htc hcc con hB hCL R R' L γ δ F base t0 t1 t2 e f g k

theorem kernelT_op_false' {A : FamilyReconstruction w ι} {i : ι} {hcan : CanonicalObject p kind A.layered}
    {hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement i) (A.family.kind i)
      (A.family.atoms i) (A.family.upper i)}
    {htc : CohOn A.layered ((A.data.tree (A.family.placement i).lower).linksAt
      (nodeSign A.skeleton.sig (A.family.placement i).lower.1)
      (inflatedPosition A.skeleton A.data.tree (A.family.placement i).lower.toNode))}
    {hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)).linksAt
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).firstLeaf A.plain).toNode)
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).secondLeaf A.plain).toNode))}
    (con : LFConstruction (A.source i hcan hel htc hcc) false)
    {T : Finset (GBranch A.skeleton.tree)} {b z : GBranch A.skeleton.tree} (hb : b = (A.family.placement i).lower)
    (hB : A.skeleton.molecule.IsBlock T b z) (hCL : Mole.CLParentPattern A.skeleton T b z)
    (R : CLRegionData A.skeleton T b z)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f g k : Mom d) :
    clLocalKernel (FamilyOperation.output (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A i)).data
        (FamilyOperation.output (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A i)).plain
        R L γ δ F (stateLayer (FamilyOperation.output
          (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A i)))
        (stateLayer_isLayering _) base t0 t1 t2 e f g k =
      clLocalKernel A.data A.plain R L γ δ F (stateLayer A) (stateLayer_isLayering A) base t0 t1 t2 e f g k := by
  subst hb
  exact kernelT_op_false A i hcan hel htc hcc con hB hCL R L γ δ F base t0 t1 t2 e f g k

section KT
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

theorem SplitAt.joint_lower : sp.sb.b = (A.family.placement pstar).lower := sp.joint.trans sp.bk

/-- A TRUE operation at `pstar` exchanges the first two boundary momenta of `K^T`. -/
theorem kT_op_true (con : LFConstruction (A.source pstar hcan hel htc hcc) true) (t : ℝ) (E F' : Mom d) :
    kT κ (FamilyOperation.output (⟨hcan, hel, htc, hcc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A pstar))
      (SplitAt.nextA A sp pstar true) t E F' = kT κ A sp t F' E :=
  kernelT_op_true' con sp.joint_lower sp.hT sp.clST.2 sp.RT (SplitAt.nextA A sp pstar true).RT κ.L κ.γ κ.δ κ.F κ.base t κ.t1 κ.t2
    E F' κ.g κ.h

/-- A FALSE operation at `pstar` leaves `K^T` unchanged. -/
theorem kT_op_false (con : LFConstruction (A.source pstar hcan hel htc hcc) false) (t : ℝ) (E F' : Mom d) :
    kT κ (FamilyOperation.output (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A pstar))
      (SplitAt.nextA A sp pstar false) t E F' = kT κ A sp t E F' := by
  have h := kernelT_op_false' con sp.joint_lower sp.hT sp.clST.2 (SplitAt.nextA A sp pstar false).RT κ.L κ.γ κ.δ κ.F κ.base t κ.t1
    κ.t2 E F' κ.g κ.h
  refine h.trans ?_
  unfold kT
  rw [regionData_subsingleton (SplitAt.nextA A sp pstar false).RT sp.RT]

end KT

end WaveTurbulence.VineEstS4
