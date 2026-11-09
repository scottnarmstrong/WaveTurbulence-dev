/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.AssemblyClocked
public import WaveTurbulence.Foundations.Vine.DegenVine.Degenerate
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS3.EpsLabels
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.AssemblyClocked
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS3.EpsLabels` (sha256 aee273959e47b3c3…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Step 3 interface to DEGEN-VINE: V4's `ε` is `epsOf` (V5, interface item 2)

Every child of a regional node `v ∈ U` is a pair leaf (a `K` row), an interior branch (an `L` row) or one of the four
boundary nodes.  `nodeOrigin` picks the source origin of a node of the local support (`clRealizedNode_sourceOrigin`
or the boundary), `originLabel` its label in `Row D ⊕ Fin 4`, and `clRegionalEpsilon_eq_epsOf` identifies V4's
`clRegionalEpsilon` with DEGEN-VINE's `epsOf` at the `sumint` boundary vector `sumintBoundary ζ (base + β)`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS3
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVine VineParamContract WaveTurbulence.GammaLow.Famb.VineEstS2
  TTree Reg Reg.Skeleton RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The label (weight row or boundary vector) of an origin. -/
noncomputable def originLabelΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (ζ : ℤˣ) :
    CLSourceOrigin R → ((assemblyShapeΓ hM9 B).VIdx ⊕ (assemblyShapeΓ hM9 B).VIdx) ⊕ Fin 4
  | .inl p => Sum.inl (Sum.inl (assemblyRowEquivΓ hM9 B p))
  | .inr (.inl v) => Sum.inl (Sum.inr (assemblyRowEquivΓ hM9 B v))
  | .inr (.inr c) => Sum.inr (sumintBoundaryPermutation ζ c)

/-- The value of an origin label at the `sumint` boundary vector is the physical origin value. -/
theorem originLabel_valueΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3)
    (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) (o : CLSourceOrigin R) :
    labMom (sourceSumintDatumΓ hM9 B hG W) L x
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)))
        (originLabelΓ hM9 B (G.sign a.toNode) o) =
      clSourceOriginValue B.isBlock R hG (assemblyIntOrderΓ hM9 B) (assemblyPairOrderΓ hG B hM9)
        (cosetDecoration G L base (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1)) o := by
  rcases o with p | v | c
  · have h := assembly_pair_momentumΓ hM9 B hG W hL base β hβ x (assemblyRowEquivΓ hM9 B p)
    simp only [originLabelΓ]
    change (sourceSumintDatumΓ hM9 B hG W).kVec L x _ (assemblyRowEquivΓ hM9 B p) = _
    rw [← h]
    simp only [clSourceOriginValue, clOrderedPairValue, clOriginValue, assemblyPairOfΓ, Equiv.symm_apply_apply,
      clPairFirstLeaf_node]
  · have h := assembly_branch_momentumΓ hM9 B hG W hL base β hβ x (assemblyRowEquivΓ hM9 B v)
    simp only [originLabelΓ]
    change (sourceSumintDatumΓ hM9 B hG W).ℓVec L x _ (assemblyRowEquivΓ hM9 B v) = _
    rw [← h]
    simp only [clSourceOriginValue, clOrderedBranchValue, assemblyBranchOfΓ, Equiv.symm_apply_apply]
  · simp only [originLabelΓ, clSourceOriginValue, cosetDecoration]
    change sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))
      (sumintBoundaryPermutation (G.sign a.toNode) c) = _
    unfold sumintBoundary
    rw [boundaryPerm_involutive]
    exact (((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).2.2.2 c).symm

/-- The label of the `j`-th child of a node. -/
noncomputable def childLabelΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (v : GBranch G.tree) (j : Fin 3) : ((assemblyShapeΓ hM9 B).VIdx ⊕ (assemblyShapeΓ hM9 B).VIdx) ⊕ Fin 4 :=
  originLabelΓ hM9 B (G.sign a.toNode) (nodeOrigin B.isBlock R hG (assemblyIntOrderΓ hM9 B) (assemblyPairOrderΓ hG B hM9) (v.child j))

/-- **V4's `ε` is DEGEN-VINE's `epsOf`.** -/
theorem clRegionalEpsilon_eq_epsOfΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3)
    (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) :
    clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1) =
      epsOf (sourceSumintDatumΓ hM9 B hG W) L (fun v : ↥U => childLabelΓ hM9 B hG v.1 0)
        (fun v : ↥U => childLabelΓ hM9 B hG v.1 1) (fun v : ↥U => childLabelΓ hM9 B hG v.1 2) x
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) := by
  set z := (clNormalizedChainEquivΓ hL B base β hβ hM9).symm x with hz
  unfold clRegionalEpsilon epsOf
  rw [← Finset.prod_coe_sort U]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hmatch : ∀ ℓ, Mole.IsInternalLeaf G U ℓ →
      cosetDecoration G L base (clExtendIndices R z.1) ℓ.toNode =
        cosetDecoration G L base (clExtendIndices R z.1) (G.pair ℓ).toNode := by
    intro ℓ hℓ
    simp only [cosetDecoration]
    rw [z.2.2.1 ℓ hℓ]
  have key : ∀ j : Fin 3, labMom (sourceSumintDatumΓ hM9 B hG W) L x
      (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) (childLabelΓ hM9 B hG v.1 j) =
      base + latticePoint L (clExtendIndices R z.1 (v.1.child j)) := by
    intro j
    unfold childLabelΓ
    rw [originLabel_valueΓ hM9 B hG W hL base β hβ x]
    exact (nodeOrigin_spec B.isBlock R hG (assemblyIntOrderΓ hM9 B) (assemblyPairOrderΓ hG B hM9) (v.1.child j) (cl_child_mem_support B.isBlock R v.2 j)
      (cosetDecoration G L base (clExtendIndices R z.1)) hmatch).symm
  rw [key 0, key 1, key 2]
  unfold epsBranch
  rw [epsMom_latticePoint hL]

end WaveTurbulence.GammaLow.Famb.VineEstS3
