/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLStep2Kernel
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAffineBoundaryRows
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLLinearSumintDatum
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SumintBoundaryNormalization

/-! # TARGET Step 2: the sumint vectors `k_v`, `ℓ_v` are the actual source momenta

For the source sumint datum, the frozen affine forms `kVec` / `ℓVec` evaluated at the
normalized lattice point `x` and at the boundary vector `sumintBoundary ζ (base + β)` are the
physical coset momenta of the first leaf of the `v`-th regional pair, respectively of the
`v`-th interior branch. -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open WaveTurbulence.VineEstS3
open VineParamContract TTree Reg Reg.Skeleton RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem gapBoundaryRow_congr {d : ℕ} (q : ℤ) (e e' : Fin 4 → Mom d) (h2 : e 2 = e' 2)
    (h3 : e 3 = e' 3) :
    ∑ c, ((gapBoundaryRow q c : ℤ) : ℝ) • e c = ∑ c, ((gapBoundaryRow q c : ℤ) : ℝ) • e' c := by
  simp only [Fin.sum_univ_four, gapBoundaryRow, h2, h3]
  norm_num

theorem latticePoint_zsmul' {d : ℕ} (L : ℝ) (m : ℤ) (n : Fin d → ℤ) :
    latticePoint L (m • n) = (m : ℝ) • latticePoint L n := by
  have := map_zsmul (latticePointAddHom (d := d) L) m n
  rw [Int.cast_smul_eq_zsmul]
  exact this

theorem latticePoint_sum' {d : ℕ} {ι : Type*} (L : ℝ) (s : Finset ι) (f : ι → (Fin d → ℤ)) :
    latticePoint L (∑ i ∈ s, f i) = ∑ i ∈ s, latticePoint L (f i) :=
  map_sum (latticePointAddHom (d := d) L) f s

/-- Common form of the pair and branch momentum identities, for a row with boundary gap `q`. -/
theorem affine_row_physical {d : ℕ} {V : Type*} [Fintype V] (L : ℝ) (base : Mom d)
    (β : Fin 4 → (Fin d → ℤ)) (e : Fin 4 → Mom d) (h2 : e 2 = base + latticePoint L (β 2))
    (h3 : e 3 = base + latticePoint L (β 3)) (q : ℤ) (T : V → ℤ) (s : V → ℤ) (x : V → (Fin d → ℤ)) :
    (∑ v', ((T v' * s v' : ℤ) : ℝ) • latticePoint L (x v')) + ∑ c, ((gapBoundaryRow q c : ℤ) : ℝ) • e c =
      base + latticePoint L ((∑ v', T v' • (s v' • x v')) + ∑ c, gapBoundaryRow q c • β c) := by
  rw [gapBoundaryRow_congr q e (fun c => base + latticePoint L (β c)) h2 h3,
    gapBoundaryRow_physical L base q β]
  have hsum : ∀ v', ((T v' * s v' : ℤ) : ℝ) • latticePoint L (x v') =
      latticePoint L (T v' • (s v' • x v')) := fun v' => by
    rw [latticePoint_zsmul', latticePoint_zsmul', smul_smul]
    push_cast
    rfl
  simp only [hsum, ← latticePoint_sum']
  rw [gapBoundaryRow_eval q β]
  simp only [latticePoint_add]
  abel

/-- The regional pair carried by the `v`-th sumint row. -/
noncomputable def assemblyPairOf (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (v : (assemblyShape hM9 B).VIdx) : ↥(clRegionalPairs hG U) :=
  (assemblyPairOrder hG B hM9).symm ((assemblyRowEquiv hM9 B).symm v)

/-- The interior branch carried by the `v`-th sumint row. -/
noncomputable def assemblyBranchOf (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (v : (assemblyShape hM9 B).VIdx) : ↥(clInteriorBranches R) :=
  (assemblyIntOrder hM9 B).e.symm ((assemblyRowEquiv hM9 B).symm v)

theorem assembly_pair_momentum (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d)
    {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
    (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)) (v : (assemblyShape hM9 B).VIdx) :
    cosetDecoration G L base
        (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
        ((assemblyPairOf hM9 B hG v).1.firstLeaf hG).toNode =
      (sourceSumintDatum hM9 B hG W).kVec L x
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v := by
  have h := clChain_pair_affine_value hL B base β hβ hM9 hG (jointFlip _ x) v
  have hv : assemblyPairValue hM9 B hG
      (clExtendIndices R ((clChainCoordinateEquiv hL B base β hβ hM9).symm (jointFlip _ x)).1) v =
      clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1
        ((assemblyPairOf hM9 B hG v).1.firstLeaf hG).toNode := by
    exact congrArg (fun z => clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1 z)
      (clPairFirstLeaf_node B.isBlock R hG (assemblyPairOf hM9 B hG v))
  have hb := sumintBoundary_lower (G.sign a.toNode) (fun j => base + latticePoint L (β j))
  unfold cosetDecoration SumintDatum.kVec
  rw [← hv, h]
  exact (affine_row_physical L base β _ hb.1 hb.2 _ (fun j => assemblyPairMatrix hM9 B hG v j)
    (fun j => jointFlipSign _ j) x).symm

theorem assembly_branch_momentum (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d)
    {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
    (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)) (v : (assemblyShape hM9 B).VIdx) :
    cosetDecoration G L base
        (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)
        (assemblyBranchOf hM9 B v).1.toNode =
      (sourceSumintDatum hM9 B hG W).ℓVec L x
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) v := by
  have h := clChain_branch_affine_value hL B base β hβ hM9 (jointFlip _ x) v
  have hv : assemblyBranchValue hM9 B
      (clExtendIndices R ((clChainCoordinateEquiv hL B base β hβ hM9).symm (jointFlip _ x)).1) v =
      clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1
        (assemblyBranchOf hM9 B v).1.toNode := rfl
  have hb := sumintBoundary_lower (G.sign a.toNode) (fun j => base + latticePoint L (β j))
  unfold cosetDecoration SumintDatum.ℓVec
  rw [← hv, h]
  exact (affine_row_physical L base β _ hb.1 hb.2 _ (fun j => assemblyBranchMatrix hM9 B v j)
    (fun j => jointFlipSign _ j) x).symm

end WaveTurbulence.VineEstS2
