/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Cls5Inj

/-! # Class combinatorics, part 5: injectivity of `sigStar` on `Zp(A)` (V5 Step 4b, WP-A)

`sigStar_output`: the signature of the output of an operation at `i`, in terms of the chosen branch / pair equivalences.
`zp_eq_of_sigStar`: two states reached from a state with a prime skeleton by a batch over `[i]` with equal `sigStar _ i` are equal.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool}

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

/-- The output state of the operation `⟨hcan, hel, htc, hcc, ε, con⟩` at `i`. -/
@[expose, reducible] noncomputable def opOut {ε : Bool} (con : LFConstruction (A.source i hcan hel htc hcc) ε) :
    FamilyReconstruction w ι :=
  FamilyOperation.output (⟨hcan, hel, htc, hcc, ε, con⟩ : FamilyOperation (p := p) (kind := kind) A i)

theorem sigStar_output {ε : Bool} (con : LFConstruction (A.source i hcan hel htc hcc) ε) :
    sigStar (opOut A i hcan hel htc hcc con) i =
      ((opOut A i hcan hel htc hcc con).skeleton.sign
          (chosenBranchEquiv A.skeleton (A.family.placement i) ε (A.family.placement i).lower).toNode,
        nativeCoupleLayered (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
          (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering _)
          (chosenPairEquiv A.skeleton (A.family.placement i) A.plain ε
            (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)),
        nativeChainLayered (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
          (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering _)
          (chosenBranchEquiv A.skeleton (A.family.placement i) ε (A.family.placement i).lower)) := by
  cases ε
  · have hq : chosenPairEquiv A.skeleton (A.family.placement i) A.plain false
        (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained) =
        pairOfLeaf A.skeleton A.plain (A.family.placement i).retained :=
      pairOfLeaf_firstLeaf A.skeleton A.plain _
    rw [hq]
    rfl
  · have hl : (A.family.nextPlacement i i).lower =
        coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement i).lower :=
      A.family.nextPlacement_lower i i
    have hr : (A.family.nextPlacement i i).retained =
        coreLeafEquiv A.skeleton (A.family.placement i) (A.family.placement i).retained :=
      A.family.nextPlacement_retained i i
    have hq : chosenPairEquiv A.skeleton (A.family.placement i) A.plain true
        (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained) =
        pairOfLeaf (unitTwistGarden A.skeleton (A.family.placement i)) (unitTwistGarden_plain _ _ A.plain)
          (coreLeafEquiv A.skeleton (A.family.placement i) (A.family.placement i).retained) :=
      sourcePairEquiv_pairOfLeaf A.plain (unitTwistGarden_plain _ _ A.plain)
        (coreLeafEquiv A.skeleton (A.family.placement i)) (fun l => (unitTwistGarden_pair _ _ l).symm) _
    unfold sigStar
    rw [Prod.mk.injEq, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · show (unitTwistGarden A.skeleton (A.family.placement i)).sign (A.family.nextPlacement i i).lower.toNode = _
      rw [hl]; rfl
    · show nativeCoupleLayered con.data _ _ _
        (pairOfLeaf (unitTwistGarden A.skeleton (A.family.placement i)) _ (A.family.nextPlacement i i).retained) = _
      rw [hr, hq]; rfl
    · show nativeChainLayered con.data _ _ _ (A.family.nextPlacement i i).lower = _
      rw [hl]; rfl

end Op


theorem sigStar_self (A : FamilyReconstruction w ι) (i : ι) :
    sigStar A i = (A.skeleton.sign (A.family.placement i).lower.toNode,
      nativeCoupleLayered A.data A.plain (stateLayer A) (stateLayer_isLayering A)
        (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained),
      nativeChainLayered A.data A.plain (stateLayer A) (stateLayer_isLayering A) (A.family.placement i).lower) := rfl

section Inj
variable (A : FamilyReconstruction w ι) (i : ι)

theorem sign_out_true (hcan : CanonicalObject p kind A.layered)
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
    (con : LFConstruction (A.source i hcan hel htc hcc) true) :
    (opOut A i hcan hel htc hcc con).skeleton.sign
      (chosenBranchEquiv A.skeleton (A.family.placement i) true (A.family.placement i).lower).toNode =
      -A.skeleton.sign (A.family.placement i).lower.toNode :=
  (coreBranchEquiv_sign A.skeleton (A.family.placement i) _).trans (if_pos rfl)

theorem units_ne_neg (u : ℤˣ) : u ≠ -u := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> decide

end Inj

end WaveTurbulence.VineEstS4
