/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Coh1

/-! # ZP-SURJ: the native data of an operation output -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5B WaveTurbulence.Stage1 WaveTurbulence.LGSpine

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool}

theorem stateLayer_congr {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    {l₁ l₂ : GNode (D.forest hS) → ℕ} (h₁ : IsLayering (D.garden hS) l₁) (h₂ : IsLayering (D.garden hS) l₂)
    (h : l₁ = l₂) (q : SourcePair S) (b : GBranch S.tree) :
    nativeCoupleLayered D hS l₁ h₁ q = nativeCoupleLayered D hS l₂ h₂ q ∧
      nativeChainLayered D hS l₁ h₁ b = nativeChainLayered D hS l₂ h₂ b := by
  subst h; exact ⟨rfl, rfl⟩

section Op
variable (A : FamilyReconstruction w ι) (i : ι)
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
  {ε : Bool} (con : LFConstruction (A.source i hcan hel htc hcc) ε)

theorem stateLayer_op : stateLayer (opOut A i hcan hel htc hcc con) = con.outLayer :=
  layeredReconstruction_inj (D := con.data) (hS := (A.source i hcan hel htc hcc).chosen_plain ε)
    (stateLayer_spec (opOut A i hcan hel htc hcc con))

theorem op_lower_eq : ((opOut A i hcan hel htc hcc con).family.placement i).lower =
    chosenBranchEquiv A.skeleton (A.family.placement i) ε (A.family.placement i).lower := by
  cases ε
  · rfl
  · exact A.family.nextPlacement_lower i i

theorem op_pair_eq : pairOfLeaf (opOut A i hcan hel htc hcc con).skeleton (opOut A i hcan hel htc hcc con).plain
    ((opOut A i hcan hel htc hcc con).family.placement i).retained =
    chosenPairEquiv A.skeleton (A.family.placement i) A.plain ε
      (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained) := by
  cases ε
  · exact (pairOfLeaf_firstLeaf A.skeleton A.plain _).symm
  · have hr : (A.family.nextPlacement i i).retained =
        coreLeafEquiv A.skeleton (A.family.placement i) (A.family.placement i).retained :=
      A.family.nextPlacement_retained i i
    have hq : chosenPairEquiv A.skeleton (A.family.placement i) A.plain true
        (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained) =
        pairOfLeaf (unitTwistGarden A.skeleton (A.family.placement i)) (unitTwistGarden_plain _ _ A.plain)
          (coreLeafEquiv A.skeleton (A.family.placement i) (A.family.placement i).retained) :=
      sourcePairEquiv_pairOfLeaf A.plain (unitTwistGarden_plain _ _ A.plain)
        (coreLeafEquiv A.skeleton (A.family.placement i)) (fun l => (unitTwistGarden_pair _ _ l).symm) _
    rw [hq]
    show pairOfLeaf (unitTwistGarden A.skeleton (A.family.placement i)) _ (A.family.nextPlacement i i).retained = _
    rw [hr]

theorem sigStar_op : sigStar (opOut A i hcan hel htc hcc con) i =
    ((opOut A i hcan hel htc hcc con).skeleton.sign
      (chosenBranchEquiv A.skeleton (A.family.placement i) ε (A.family.placement i).lower).toNode,
      conLQ con, conLX con) := by
  rw [sigStar_output]
  have hs := stateLayer_op A i hcan hel htc hcc con
  have := stateLayer_congr (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
    (stateLayer_isLayering _) con.out_isLayering hs
    (chosenPairEquiv A.skeleton (A.family.placement i) A.plain ε
      (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained))
    (chosenBranchEquiv A.skeleton (A.family.placement i) ε (A.family.placement i).lower)
  rw [this.1, this.2]
  rfl

end Op

end WaveTurbulence.ZpSurj
