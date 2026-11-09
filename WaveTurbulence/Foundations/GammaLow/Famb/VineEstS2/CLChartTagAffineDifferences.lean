/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChartSourceAffineRows
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLCoordinateChartTagDifferences
public import WaveTurbulence.Foundations.VineEst.VineEstS2.SourceBoundaryBasis
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChartTagAffineDifferences
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChartSourceAffineRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLCoordinateChartTagDifferences
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLChartTagAffineDifferences` (sha256 9df4ab620fde6cb5…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Source coordinate differences are identities of exact affine forms -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- Uniform original source-label differences determine both the free
matrix and all four affine boundary coefficients in frozen sumint(iii). -/
theorem exists_chartTag_affine_differenceΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (v : (assemblyShapeΓ hM9 B).VIdx) :
    ∃ p q : CLChartSourceTag R,
      (∀ j, sourceRowTΓ hM9 B hG (chartSourceTag R p) j-sourceRowTΓ hM9 B hG (chartSourceTag R q) j = if j = v then 1 else 0) ∧
      ∀ c, sourceRowHΓ hM9 B hG (chartSourceTag R p) c-sourceRowHΓ hM9 B hG (chartSourceTag R q) c = 0 := by
  classical
  obtain ⟨p,q,hpq⟩ := clChainCoordinate_chartTag_differenceΓ hM9 B hG v
  have hform {d : ℕ} (β : Fin 4 → (Fin d → ℤ))
      (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3)
      (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) :
      x v = ((∑ j, sourceRowTΓ hM9 B hG (chartSourceTag R p) j • x j)+
        ∑ c, sourceRowHΓ hM9 B hG (chartSourceTag R p) c • β c) -
      ((∑ j, sourceRowTΓ hM9 B hG (chartSourceTag R q) j • x j)+
        ∑ c, sourceRowHΓ hM9 B hG (chartSourceTag R q) c • β c) := by
    exact (hpq (L := 1) one_ne_zero (0 : Mom d) β hβ x).trans
      (congrArg₂ (fun y z : Fin d → ℤ => y-z)
        (chartSource_origin_affineΓ (L := 1) one_ne_zero B (0 : Mom d) β hβ hM9 hG x p)
        (chartSource_origin_affineΓ (L := 1) one_ne_zero B (0 : Mom d) β hβ hM9 hG x q))
  refine ⟨p,q,?_,?_⟩
  · intro j
    let x : (assemblyShapeΓ hM9 B).VIdx → (Fin 1 → ℤ) := fun u _ => if u = j then 1 else 0
    have hβ : ((G.sign a.toNode : ℤ) • ((0 : Fin 4 → (Fin 1 → ℤ)) 0-0)) = 0-0 := by simp
    have he := congrArg (fun f : Fin 1 → ℤ => f 0) (hform 0 hβ x)
    have hsum (f : (assemblyShapeΓ hM9 B).VIdx → ℤ) : ((∑ u, f u • x u) : Fin 1 → ℤ) 0 = f j := by
      simp [x,Finset.sum_apply,Pi.smul_apply]
    have hv : x v 0 = if v = j then 1 else 0 := rfl
    have hh : (if v = j then (1 : ℤ) else 0) =
        sourceRowTΓ hM9 B hG (chartSourceTag R p) j-sourceRowTΓ hM9 B hG (chartSourceTag R q) j := by
      simpa only [Pi.zero_apply,smul_zero,Finset.sum_const_zero,add_zero,Pi.sub_apply,hsum,hv] using he
    exact hh.symm.trans (by
      by_cases h : j = v
      · simp [h]
      · simp [h,Ne.symm h])
  · intro c
    let β := sourceBoundaryBasis (G.sign a.toNode) c
    have he := congrArg (fun f : Fin 1 → ℤ => f 0)
      (hform β (sourceBoundaryBasis_conservation _ c) 0)
    have hp : ((∑ j, sourceRowHΓ hM9 B hG (chartSourceTag R p) j • β j) : Fin 1 → ℤ) 0 =
        sourceRowHΓ hM9 B hG (chartSourceTag R p) c :=
      sourceBoundaryBasis_eval _ c _ (sourceRowH_chartTag_upper_zeroΓ hM9 B hG p)
    have hq : ((∑ j, sourceRowHΓ hM9 B hG (chartSourceTag R q) j • β j) : Fin 1 → ℤ) 0 =
        sourceRowHΓ hM9 B hG (chartSourceTag R q) c :=
      sourceBoundaryBasis_eval _ c _ (sourceRowH_chartTag_upper_zeroΓ hM9 B hG q)
    simpa only [Pi.zero_apply,smul_zero,Finset.sum_const_zero,zero_add,Pi.sub_apply,hp,hq] using he.symm

end WaveTurbulence.GammaLow.Famb.VineEstS2
