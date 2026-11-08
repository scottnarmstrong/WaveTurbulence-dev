/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5WB.B.WeightOp
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Rg1Geom
public import WaveTurbulence.Foundations.Molecule.TwistChildLabels
public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot8
public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitSummand
public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitGeom2

/-! # V5W-T A3 (part 1): the top-weighted bond weight and its transport

The member weight of the pinned class kernel at `S = some s` is the masked, normalized bond weight of the member's
region times the top filter at the member's region top: `bWT ψ W κ X U a = bWN ψ κ X U · nodeWeight W L base a`
(V5W-0's `regionWeightFW` with the row normalization moved to the multiplier, as in V5W-B-WORLD's `bWN`).

The node weight at a block top is transported exactly by every family operation used in the class identity:
* `nodeWeight_twist`, `coset_twistNodeLabels` (uni-space `VineSpaceK/NodeWeight.lean`, `BranchWeight.lean`): a unit
  twist at a placement whose lower joint is not the node;
* `nodeWeight_rigid` (uni-space `VineSpaceK/WeightedSSum.lean`): a rigid twist below the block, any upper atom.
Copied by source (sha256 in `COPIED-SHA256SUMS`).  With V5W-B-WORLD's `bWN_false`, `bWN_rigid`, `bWN_twist` they give
`bWT_false`, `bWT_rigid`, `bWT_twist`.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.V5WT
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS4 VineEstS5B Links
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (nodeWeight)
variable {w d : ℕ} {ι : Type*}

section Node
variable {G : Garden w}

theorem coset_twistNodeLabels (P : CorePlacement G) (L : ℝ) (base : Mom d)
    (x : GNode G.tree → Fin d → ℤ) :
    cosetDecoration (unitTwistGarden G P) L base (twistNodeLabels G P x) =
      twistNodeLabels G P (cosetDecoration G L base x) := by
  funext n
  unfold cosetDecoration twistNodeLabels switchedOldLabels
  split_ifs <;> rfl

theorem nodeWeight_twist (P : CorePlacement G) (W : (Fin 4 → Mom d) → ℂ)
    (L : ℝ) (base : Mom d) (x : GNode G.tree → Fin d → ℤ)
    (hx : PairedAt P x) (v : GBranch G.tree) (hv : v ≠ P.lower) :
    nodeWeight W L base (coreBranchEquiv G P v) (twistNodeLabels G P x) =
      nodeWeight W L base v x := by
  unfold nodeWeight
  rw [coset_twistNodeLabels]
  have hp : cosetDecoration G L base x P.retained.toNode =
      cosetDecoration G L base x (G.pair P.retained).toNode :=
    congrArg (fun z => base + latticePoint L z) hx
  apply congrArg W
  funext i
  fin_cases i
  · exact twistNodeLabels_branch G P _ v hv
  · exact twistNodeLabels_other_child G P _ hp v hv 0
  · exact twistNodeLabels_other_child G P _ hp v hv 1
  · exact twistNodeLabels_other_child G P _ hp v hv 2

theorem nodeWeight_rigid (P : CorePlacement G)
    {S : Finset (GBranch G.tree)} {b : GBranch G.tree} (hR : RigidAt P S b)
    (W : (Fin 4 → Mom d) → ℂ) (L : ℝ) (base : Mom d)
    (x' : GNode (unitTwistGarden G P).tree → Fin d → ℤ)
    {v : GBranch G.tree} (hv : v ∈ S.erase b) :
    nodeWeight W L base (coreBranchEquiv G P v) x' =
      nodeWeight W L base v (fun y => x' (naiveNodeEquiv G P y)) := by
  unfold nodeWeight cosetDecoration
  simp only [hR.child_naive hv, naiveNodeEquiv_branch G P v]
  rfl

end Node

section Glue
open VineEstS4
variable {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

/-- The node weight at the upper top depends only on the S side of the glue (uni-space `VineSpaceK/WeightedSplit`). -/
theorem nodeWeight_glue (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c)
    (hi : S ∩ T = {b}) (hU : G.molecule.IsBlock (S ∪ T) a c)
    (RS : CLRegionData G S a b) (W : (Fin 4 → Mom d) → ℂ) (L : ℝ) (base : Mom d)
    (x y : GNode G.tree → Fin d → ℤ) :
    nodeWeight W L base a (glue RS x y) = nodeWeight W L base a x := by
  unfold nodeWeight cosetDecoration
  simp only [glue_A RS x y (splitA_node hS hT hi hU RS hS.2.1),
    glue_A RS x y (splitA_child hS hT hi hU RS hS.2.1 hS.2.2.2.1 _)]

/-- The node weight at the upper top is read on the upper restriction (uni-space `VineSpaceK/WeightedFlatMerge`). -/
theorem nodeWeight_rA (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c)
    (hi : S ∩ T = {b}) (hU : G.molecule.IsBlock (S ∪ T) a c)
    (RS : CLRegionData G S a b) (W : (Fin 4 → Mom d) → ℂ) (L : ℝ) (base : Mom d)
    (x : GNode G.tree → Fin d → ℤ) :
    nodeWeight W L base a (rA RS x) = nodeWeight W L base a x := by
  unfold nodeWeight cosetDecoration rA
  simp only [splitA_node hS hT hi hU RS hS.2.1, splitA_child hS hT hi hU RS hS.2.1 hS.2.2.2.1, ite_true]

end Glue

/-- **The top-weighted bond weight**: the masked, normalized bond weight of the region `U` times the node weight `W`
at the region top `a`. -/
def bWT (ψ : WD d) (W : (Fin 4 → Mom d) → ℂ) (κ : KPar d) (X : FamilyReconstruction w ι)
    (U : Finset (GBranch X.skeleton.tree)) (a : GBranch X.skeleton.tree) (x : GNode X.skeleton.tree → Fin d → ℤ) : ℂ :=
  bWN ψ κ X U x * nodeWeight W κ.L κ.base a x

theorem norm_bWT_le (ψ : WD d) (W : (Fin 4 → Mom d) → ℂ) (κ : KPar d) (X : FamilyReconstruction w ι)
    (U : Finset (GBranch X.skeleton.tree)) (a : GBranch X.skeleton.tree) {C CW : ℝ} (hψ : ∀ q q' k, ‖ψ.ψ q q' k‖ ≤ C)
    (hW : ∀ z, ‖W z‖ ≤ CW) (x : GNode X.skeleton.tree → Fin d → ℤ) :
    ‖bWT ψ W κ X U a x‖ ≤ bWNB ψ X U C * CW := by
  unfold bWT
  rw [norm_mul]
  exact mul_le_mul (norm_bWN_le ψ κ X U C hψ x) (hW _) (norm_nonneg _)
    ((norm_nonneg _).trans (norm_bWN_le ψ κ X U C hψ x))

section Op
variable {p : ℕ} {kind : Bool} (A : FamilyReconstruction w ι) (i : ι)
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

/-- Same chart: a FALSE operation keeps the top-weighted weight of every block. -/
theorem bWT_false (ψ : WD d) (W : (Fin 4 → Mom d) → ℂ) (κ : KPar d)
    (con : LFConstruction (A.source i hcan hel htc hcc) false)
    (U : Finset (GBranch A.skeleton.tree)) (a : GBranch A.skeleton.tree) :
    bWT ψ W κ (opOut A i hcan hel htc hcc con) U a = bWT ψ W κ A U a := by
  funext x
  unfold bWT
  rw [bWN_false A i hcan hel htc hcc ψ κ con U]
  rfl

/-- Rigid transport: a TRUE operation whose lower joint is outside the block; the top is an upper atom. -/
theorem bWT_rigid (ψ : WD d) (W : (Fin 4 → Mom d) → ℂ) (κ : KPar d)
    (con : LFConstruction (A.source i hcan hel htc hcc) true)
    {U : Finset (GBranch A.skeleton.tree)} {a b : GBranch A.skeleton.tree} (hR : RigidAt (A.family.placement i) U b)
    (ha : a ∈ U.erase b) (x') :
    bWT ψ W κ (opOut A i hcan hel htc hcc con) (twistedAtoms A.skeleton (A.family.placement i) U)
        (coreBranchEquiv A.skeleton (A.family.placement i) a) x' =
      bWT ψ W κ A U a (fun y => x' (naiveNodeEquiv A.skeleton (A.family.placement i) y)) := by
  unfold bWT
  rw [bWN_rigid A i hcan hel htc hcc ψ κ con hR.lower_notMem x']
  congr 1
  exact nodeWeight_rigid (A.family.placement i) hR W κ.L κ.base x' ha

/-- The twist at the lower joint of the block: the top is not the lower joint. -/
theorem bWT_twist (ψ : WD d) (W : (Fin 4 → Mom d) → ℂ) (κ : KPar d)
    (con : LFConstruction (A.source i hcan hel htc hcc) true)
    (U : Finset (GBranch A.skeleton.tree)) (a : GBranch A.skeleton.tree) (ha : a ≠ (A.family.placement i).lower)
    (x : GNode A.skeleton.tree → Fin d → ℤ) (hx : PairedAt (A.family.placement i) x) :
    bWT ψ W κ (opOut A i hcan hel htc hcc con) (twistedAtoms A.skeleton (A.family.placement i) U)
        (coreBranchEquiv A.skeleton (A.family.placement i) a)
        (twistNodeLabels A.skeleton (A.family.placement i) x) = bWT ψ W κ A U a x := by
  unfold bWT
  rw [bWN_twist A i hcan hel htc hcc ψ κ con U x hx]
  congr 1
  exact nodeWeight_twist (A.family.placement i) W κ.L κ.base x hx a ha

end Op

end WaveTurbulence.Flower.V5WT
