/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLFrozenFormRows
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChartTagAffineDifferences
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLFrozenAffineDifferences
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChartTagAffineDifferences
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLFrozenFormRows
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLFrozenAffineDifferences` (sha256 2653d9f8db60e98c…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Exact frozen sumint(iii) for the normalized original source matrices -/

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

theorem raw_affine_difference_systemΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (v : (assemblyShapeΓ hM9 B).VIdx) :
    ∃ p q : (assemblyShapeΓ hM9 B).VIdx ⊕ (assemblyShapeΓ hM9 B).VIdx ⊕ Fin 4,
      (∀ j, sumintFormRowT (assemblyPairMatrixΓ hM9 B hG) (assemblyBranchMatrixΓ hM9 B) p j -
        sumintFormRowT (assemblyPairMatrixΓ hM9 B hG) (assemblyBranchMatrixΓ hM9 B) q j = if j = v then 1 else 0) ∧
      ∀ c, sumintFormRowH (assemblyPairBoundaryRowΓ hM9 B hG) (assemblyBranchBoundaryRowΓ hM9 B) p c -
        sumintFormRowH (assemblyPairBoundaryRowΓ hM9 B hG) (assemblyBranchBoundaryRowΓ hM9 B) q c = 0 := by
  obtain ⟨p,q,hT,hH⟩ := exists_chartTag_affine_differenceΓ hM9 B hG v
  refine ⟨chartSourceFrozenTagΓ hM9 B p,chartSourceFrozenTagΓ hM9 B q,?_,?_⟩
  · simpa only [formRowT_chartSourceTagΓ] using hT
  · simpa only [formRowH_chartSourceTagΓ] using hH

/-- This is word-for-word the free and all-four-boundary affine form
condition in frozen Admissible(iii), after the source gap involution. -/
theorem normalized_affine_difference_systemΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (v : (assemblyShapeΓ hM9 B).VIdx) :
    ∃ p q : (assemblyShapeΓ hM9 B).VIdx ⊕ (assemblyShapeΓ hM9 B).VIdx ⊕ Fin 4,
      (∀ j, sumintFormRowT (normalizedPairMatrixΓ hM9 B hG) (normalizedBranchMatrixΓ hM9 B) p j -
        sumintFormRowT (normalizedPairMatrixΓ hM9 B hG) (normalizedBranchMatrixΓ hM9 B) q j = if j = v then 1 else 0) ∧
      ∀ c, sumintFormRowH (assemblyPairBoundaryRowΓ hM9 B hG) (assemblyBranchBoundaryRowΓ hM9 B) p c -
        sumintFormRowH (assemblyPairBoundaryRowΓ hM9 B hG) (assemblyBranchBoundaryRowΓ hM9 B) q c = 0 := by
  obtain ⟨p,q,hT,hH⟩ := raw_affine_difference_systemΓ hM9 B hG v
  by_cases hv : v.2.val = 0
  · refine ⟨q,p,?_,?_⟩
    · intro j
      rw [normalized_formRowTΓ,normalized_formRowTΓ,← sub_mul]
      have he : sumintFormRowT (assemblyPairMatrixΓ hM9 B hG) (assemblyBranchMatrixΓ hM9 B) q j -
          sumintFormRowT (assemblyPairMatrixΓ hM9 B hG) (assemblyBranchMatrixΓ hM9 B) p j = -(if j = v then 1 else 0) := by
        have hh := hT j
        omega
      rw [he]
      by_cases hj : j = v
      · subst j
        simp [jointFlipSign,hv]
      · simp only [hj,ite_false,neg_zero,zero_mul]
    · intro c
      have he := hH c
      omega
  · refine ⟨p,q,?_,hH⟩
    intro j
    rw [normalized_formRowTΓ,normalized_formRowTΓ,← sub_mul,hT j]
    by_cases hj : j = v
    · subst j
      simp [jointFlipSign,hv]
    · simp only [hj,ite_false,zero_mul]

end WaveTurbulence.GammaLow.Famb.VineEstS2
