/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.HFree

/-! # W2-HFREE (1): operativity at the start state, placement uniqueness

`lvOp_iff`: a member `j` of a level is operative at the level state iff `e j` is operative at the start state
(every level state is a restriction of the start state, with the same layered garden and reconstruction data).
`topOp_of_ready`: canonical + source-layer eligible + both coherences give an operation (identity construction).
`placement_unique`: two placements at the same atoms and lower joint are equal.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P4.Bot

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n p : ℕ} {kind : Bool}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- A core member is operative at the start state. -/
def TopOp (i : (assemblySourceFamily B).CoreIndex) : Prop :=
  Nonempty (FamilyOperation (p := p) (kind := kind) (startState B RD hG layer hLayer) i)

theorem lvOp_iff (lv : Lvl B) (j : lv.ι) :
    lv.Op (p := p) (kind := kind) B RD hG layer hLayer j ↔ TopOp (p := p) (kind := kind) B RD hG layer hLayer (lv.e j) :=
  ⟨fun ⟨op⟩ => ⟨opOfRestrict _ lv.e lv.he op⟩, fun ⟨op⟩ => ⟨opToRestrict _ lv.e lv.he op⟩⟩

theorem topOp_of_ready {ι : Type*} {kind : Bool} (A : FamilyReconstruction w ι) (i : ι)
    (hcan : CanonicalObject p kind A.layered)
    (helig : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement i)
      (A.family.kind i) (A.family.atoms i) (A.family.upper i))
    (ht : CohOn A.layered ((A.data.tree (A.family.placement i).lower).linksAt
      (nodeSign A.skeleton.sig (A.family.placement i).lower.1)
      (inflatedPosition A.skeleton A.data.tree (A.family.placement i).lower.toNode)))
    (hq : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)).linksAt
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).firstLeaf A.plain).toNode)
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).secondLeaf A.plain).toNode))) :
    Nonempty (FamilyOperation (p := p) (kind := kind) A i) := by
  obtain ⟨h, _⟩ := (A.source (p := p) (kind := kind) i hcan helig ht hq).identity_construction
  exact ⟨⟨hcan, helig, ht, hq, false, h⟩⟩

theorem placement_unique {S : Finset (GBranch G.tree)} {c : GBranch G.tree} {P Q : CorePlacement G}
    (hP : IsPlacementAt G S c P) (hQ : IsPlacementAt G S c Q) : P = Q := by
  have hk : P.keep = Q.keep := by
    have h1 := (hP.2 P.keep).mpr rfl
    exact ((hQ.2 P.keep).mp h1)
  have hl : P.lower = Q.lower := hP.1.trans hQ.1.symm
  have hr : P.retained = Q.retained := by
    have h1 := P.child
    have h2 := Q.child
    have hn : P.retained.toNode = Q.retained.toNode := by
      rw [h1, h2, hl, hk]
    exact Subtype.ext (congrArg (fun x : GNode G.tree => x.1) hn)
  exact CorePlacement.ext_data hl hr hk

end WaveTurbulence.VineEstS5C.P4.W2
