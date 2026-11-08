/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.BondSplit
public import WaveTurbulence.Foundations.VineEst.VineSpaceB.BondStatements
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Cls6Zp
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw9Native

/-! # V5-SPACE-EXT: the bond weight of a state, and its transport along family operations

`layX X`: the core layering of the skeleton of a state; `bW ψ κ X U`: the bond weight of the block `U` of `X`.
A TRUE operation transports the core layers along the branch bijection, a FALSE one keeps them
(`LFConstruction.coreLayers`, through `coreLayer_eq`). Combined with the molecule isomorphism (`VineSpaceB.Bond`)
this gives the four transports used by the weighted recursion: rigid (operation below the block), same chart,
twist at the lower joint of the block (S side), twist above the block (T side). -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.VineSpaceB
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS4 VineEstS5B VineSpaceK Links

variable {w d : ℕ} {ι : Type*}

/-- The core (skeleton) layering of a state. -/
def layX (X : FamilyReconstruction w ι) (v : GBranch X.skeleton.tree) : ℕ :=
  stateLayer X (X.data.coreBranch X.plain v).toNode

/-- The bond weight of the block `U` of a state, at the lattice parameters of `κ`. -/
def bW (ψ : ℕ → ℕ → Mom d → ℂ) (κ : KPar d) (X : FamilyReconstruction w ι) (U : Finset (GBranch X.skeleton.tree)) :
    (GNode X.skeleton.tree → Fin d → ℤ) → ℂ :=
  bondW ψ κ.L κ.base X.skeleton (layX X) U

/-- The weighted member kernel of a state at a region. -/
def memberB (κ : KPar d) (lam : ℝ) (ψ : ℕ → ℕ → Mom d → ℂ) (X : FamilyReconstruction w ι)
    (c : ChainAt X.skeleton X.family) : ℂ :=
  memberMX X.data X.plain (clRegionData X.skeleton c.block c.cl) κ.L κ.γ κ.δ κ.F
    (stateLayer X) (stateLayer_isLayering X) κ.base lam (bW ψ κ X c.U) κ.t0 κ.t1 κ.t2 κ.e κ.f κ.g κ.h

theorem memberCoreLayer_eq (z : ClassMember w ι) (v : GBranch z.1.skeleton.tree) :
    memberCoreLayer z v = layX z.1 v := by
  unfold memberCoreLayer layX
  rw [← stateLayer_spec z.1]
  exact layerAt_node (layeredReconstruction z.1.data z.1.plain (stateLayer z.1) (stateLayer_isLayering z.1))
    (z.1.data.coreBranch z.1.plain v).toNode

/-- The statement's multiplier is the bond weight of the member's region. -/
theorem regionBondWeight_eq (ψ : ℕ → ℕ → Mom d → ℂ) (L : ℝ) (base : Mom d) (z : ClassMember w ι) :
    regionBondWeight ψ L base z = bondW ψ L base z.1.skeleton (layX z.1) z.2.U := by
  funext x
  unfold regionBondWeight bondW regionDarts
  refine Finset.prod_congr rfl fun y _ => ?_
  rw [memberCoreLayer_eq, memberCoreLayer_eq]

theorem norm_bW_le (ψ : ℕ → ℕ → Mom d → ℂ) (κ : KPar d) (X : FamilyReconstruction w ι)
    (U : Finset (GBranch X.skeleton.tree)) (C : ℝ) (hψ : ∀ q q' k, ‖ψ q q' k‖ ≤ C) (x) :
    ‖bW ψ κ X U x‖ ≤ C ^ (regionDarts X.skeleton U).card :=
  norm_bondW_le ψ κ.L κ.base X.skeleton (layX X) U x C hψ

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

/-- A TRUE operation transports the core layers. -/
theorem layX_true (con : LFConstruction (A.source i hcan hel htc hcc) true) (v : GBranch A.skeleton.tree) :
    layX (opOut A i hcan hel htc hcc con) (coreBranchEquiv A.skeleton (A.family.placement i) v) = layX A v :=
  coreLayer_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
    (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
    (stateLayer_spec (opOut A i hcan hel htc hcc con)) v

/-- A FALSE operation keeps the core layers. -/
theorem layX_false (con : LFConstruction (A.source i hcan hel htc hcc) false) (v : GBranch A.skeleton.tree) :
    layX (opOut A i hcan hel htc hcc con) v = layX A v :=
  coreLayer_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
    (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
    (stateLayer_spec (opOut A i hcan hel htc hcc con)) v

/-- Same chart: a FALSE operation keeps the bond weight of every block. -/
theorem bW_false (ψ : ℕ → ℕ → Mom d → ℂ) (κ : KPar d) (con : LFConstruction (A.source i hcan hel htc hcc) false)
    (U : Finset (GBranch A.skeleton.tree)) :
    bW ψ κ (opOut A i hcan hel htc hcc con) U = bW ψ κ A U := by
  funext x
  exact bondW_congr ψ κ.L κ.base A.skeleton U (fun v _ => layX_false A i hcan hel htc hcc con v) (fun _ _ => rfl)

/-- Rigid transport: a TRUE operation whose lower joint is outside the block. -/
theorem bW_rigid (ψ : ℕ → ℕ → Mom d → ℂ) (κ : KPar d) (con : LFConstruction (A.source i hcan hel htc hcc) true)
    {U : Finset (GBranch A.skeleton.tree)} (hlow : (A.family.placement i).lower ∉ U) (x') :
    bW ψ κ (opOut A i hcan hel htc hcc con) (twistedAtoms A.skeleton (A.family.placement i) U) x' =
      bW ψ κ A U (fun y => x' (naiveNodeEquiv A.skeleton (A.family.placement i) y)) :=
  bondW_naive ψ κ.L κ.base (A.family.placement i) (layX A) (layX (opOut A i hcan hel htc hcc con)) hlow x'
    (fun v _ => layX_true A i hcan hel htc hcc con v)

/-- The twist at the lower joint of the block (S side, and the bottom vine of a region). -/
theorem bW_twist (ψ : ℕ → ℕ → Mom d → ℂ) (κ : KPar d) (con : LFConstruction (A.source i hcan hel htc hcc) true)
    (U : Finset (GBranch A.skeleton.tree)) (x : GNode A.skeleton.tree → Fin d → ℤ)
    (hx : PairedAt (A.family.placement i) x) :
    bW ψ κ (opOut A i hcan hel htc hcc con) (twistedAtoms A.skeleton (A.family.placement i) U)
        (twistNodeLabels A.skeleton (A.family.placement i) x) = bW ψ κ A U x :=
  bondW_twist ψ κ.L κ.base (A.family.placement i) (layX A) (layX (opOut A i hcan hel htc hcc con)) U x hx
    (fun v _ => layX_true A i hcan hel htc hcc con v)

/-- The twist above the block (T side): the labels are read through `twNode`. -/
theorem bW_twNode (ψ : ℕ → ℕ → Mom d → ℂ) (κ : KPar d) (con : LFConstruction (A.source i hcan hel htc hcc) true)
    {T : Finset (GBranch A.skeleton.tree)}
    (hpar : GNode.parent (A.family.placement i).lower.toNode (A.family.placement i).nonroot ∉ T)
    (hret : ¬ A.skeleton.molecule.InGroup T (retainedLP A.skeleton (A.family.placement i))) (x') :
    bW ψ κ (opOut A i hcan hel htc hcc con) (twistedAtoms A.skeleton (A.family.placement i) T) x' =
      bW ψ κ A T (fun y => x' (twNode (A.family.placement i) y)) :=
  bondW_twNode ψ κ.L κ.base (A.family.placement i) (layX A) (layX (opOut A i hcan hel htc hcc con)) hpar hret x'
    (fun v _ => layX_true A i hcan hel htc hcc con v)

end Op

end WaveTurbulence.VineSpaceB
