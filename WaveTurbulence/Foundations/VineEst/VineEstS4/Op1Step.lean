/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp1Geom
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Class

/-! # One LF operation: the S-side and the T-side of (tildeJ2) (V5 Step 4b, step 4)

For a state `A` and the operation `⟨hcan, hel, htc, hcc, ε, con⟩` at the member `i` (output state `X'`):

* `sSum_op_true` / `sSum_op_false`: the S-side `sSum` with an arbitrary lower factor `Φ`, at the upper block `S` and its image
  (`twistedAtoms S` for `ε = true`, `S` for `ε = false`), with the boundary nodes `b`, `b.child kept` of the respective gardens, is the same for `A` and `X'`
  provided `S` is rigid (`RigidAt`) for a TRUE operation (lower joint of the placement not in `S` for a false one).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} (A : FamilyReconstruction w ι) (i : ι)
  (hcan : CanonicalObject p kind A.layered)
  (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement i) (A.family.kind i)
    (A.family.atoms i) (A.family.upper i))
  (htc : CohOn A.layered ((A.data.tree (A.family.placement i).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement i).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement i).lower.toNode)))
  (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).secondLeaf A.plain).toNode)))

/-- **S-side of a TRUE operation at a member below the split.** -/
theorem sSum_op_true (con : LFConstruction (A.source i hcan hel htc hcc) true)
    {S : Finset (GBranch A.skeleton.tree)} {a b : GBranch A.skeleton.tree} (hS : A.skeleton.molecule.IsBlock S a b)
    (hR : RigidAt (A.family.placement i) S b) (RS : CLRegionData A.skeleton S a b)
    (RS' : CLRegionData (unitTwistGarden A.skeleton (A.family.placement i))
      (twistedAtoms A.skeleton (A.family.placement i) S) (eB (A.family.placement i) a) (eB (A.family.placement i) b))
    {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f : Mom d)
    (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSum RS' (FamilyOperation.output (⟨hcan, hel, htc, hcc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i)).data
        (FamilyOperation.output (⟨hcan, hel, htc, hcc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i)).plain
        L γ δ F (stateLayer (FamilyOperation.output
          (⟨hcan, hel, htc, hcc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i)))
        (stateLayer_isLayering _) base t0 t1 t2 e f
        (eB (A.family.placement i) b).toNode ((eB (A.family.placement i) b).child RS'.kept) Φ =
      sSum RS A.data A.plain L γ δ F (stateLayer A) (stateLayer_isLayering A) base t0 t1 t2 e f
        b.toNode (b.child RS.kept) Φ := by
  have hk : RS'.kept = RS.kept := kept_eq_rigid (A.family.placement i) hS hR RS RS'
  have n0 : naiveNodeEquiv A.skeleton (A.family.placement i) b.toNode = (eB (A.family.placement i) b).toNode :=
    naiveNodeEquiv_branch _ _ b
  have n1 : naiveNodeEquiv A.skeleton (A.family.placement i) (b.child RS.kept) =
      (eB (A.family.placement i) b).child RS'.kept := by
    rw [hk]
    exact hR.child_naive_real hS.2.2.1 (cl_child_mem_realization_of_internal hS RS hS.2.2.1 RS.kept ((RS.lower RS.kept).mpr rfl))
  rw [← n0, ← n1]
  exact sSum_rigid_LF (A.source i hcan hel htc hcc) con hS hR RS RS' _ _ (stateLayer_spec A) _ _
    (stateLayer_spec (FamilyOperation.output (⟨hcan, hel, htc, hcc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i)))
    L γ δ F base t0 t1 t2 e f b.toNode (b.child RS.kept) Φ

/-- **S-side of a FALSE operation** (same skeleton and regions; only `lower ∉ S` is needed). -/
theorem sSum_op_false (con : LFConstruction (A.source i hcan hel htc hcc) false)
    {S : Finset (GBranch A.skeleton.tree)} {a b : GBranch A.skeleton.tree}
    (hlow : (A.family.placement i).lower ∉ S) (RS : CLRegionData A.skeleton S a b)
    {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f : Mom d)
    (n0 n1 : GNode A.skeleton.tree) (Φ : ℝ → Mom d → Mom d → ℂ) :
    sSum RS (FamilyOperation.output (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A i)).data
        (FamilyOperation.output (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A i)).plain
        L γ δ F (stateLayer (FamilyOperation.output
          (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A i)))
        (stateLayer_isLayering _) base t0 t1 t2 e f n0 n1 Φ =
      sSum RS A.data A.plain L γ δ F (stateLayer A) (stateLayer_isLayering A) base t0 t1 t2 e f n0 n1 Φ :=
  sSum_false_LF (A.source i hcan hel htc hcc) con hlow RS _ _ (stateLayer_spec A) _ _
    (stateLayer_spec (FamilyOperation.output (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A i)))
    L γ δ F base t0 t1 t2 e f n0 n1 Φ

end WaveTurbulence.VineEstS4
