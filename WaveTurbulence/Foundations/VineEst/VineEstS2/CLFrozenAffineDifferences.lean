/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLFrozenFormRows
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChartTagAffineDifferences

/-! # Exact frozen sumint(iii) for the normalized original source matrices -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem raw_affine_difference_system (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (v : (assemblyShape hM9 B).VIdx) :
    ∃ p q : (assemblyShape hM9 B).VIdx ⊕ (assemblyShape hM9 B).VIdx ⊕ Fin 4,
      (∀ j, sumintFormRowT (assemblyPairMatrix hM9 B hG) (assemblyBranchMatrix hM9 B) p j -
        sumintFormRowT (assemblyPairMatrix hM9 B hG) (assemblyBranchMatrix hM9 B) q j = if j = v then 1 else 0) ∧
      ∀ c, sumintFormRowH (assemblyPairBoundaryRow hM9 B hG) (assemblyBranchBoundaryRow hM9 B) p c -
        sumintFormRowH (assemblyPairBoundaryRow hM9 B hG) (assemblyBranchBoundaryRow hM9 B) q c = 0 := by
  obtain ⟨p,q,hT,hH⟩ := exists_chartTag_affine_difference hM9 B hG v
  refine ⟨chartSourceFrozenTag hM9 B p,chartSourceFrozenTag hM9 B q,?_,?_⟩
  · simpa only [formRowT_chartSourceTag] using hT
  · simpa only [formRowH_chartSourceTag] using hH

/-- This is word-for-word the free and all-four-boundary affine form
condition in frozen Admissible(iii), after the source gap involution. -/
theorem normalized_affine_difference_system (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (v : (assemblyShape hM9 B).VIdx) :
    ∃ p q : (assemblyShape hM9 B).VIdx ⊕ (assemblyShape hM9 B).VIdx ⊕ Fin 4,
      (∀ j, sumintFormRowT (normalizedPairMatrix hM9 B hG) (normalizedBranchMatrix hM9 B) p j -
        sumintFormRowT (normalizedPairMatrix hM9 B hG) (normalizedBranchMatrix hM9 B) q j = if j = v then 1 else 0) ∧
      ∀ c, sumintFormRowH (assemblyPairBoundaryRow hM9 B hG) (assemblyBranchBoundaryRow hM9 B) p c -
        sumintFormRowH (assemblyPairBoundaryRow hM9 B hG) (assemblyBranchBoundaryRow hM9 B) q c = 0 := by
  obtain ⟨p,q,hT,hH⟩ := raw_affine_difference_system hM9 B hG v
  by_cases hv : v.2.val = 0
  · refine ⟨q,p,?_,?_⟩
    · intro j
      rw [normalized_formRowT,normalized_formRowT,← sub_mul]
      have he : sumintFormRowT (assemblyPairMatrix hM9 B hG) (assemblyBranchMatrix hM9 B) q j -
          sumintFormRowT (assemblyPairMatrix hM9 B hG) (assemblyBranchMatrix hM9 B) p j = -(if j = v then 1 else 0) := by
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
    rw [normalized_formRowT,normalized_formRowT,← sub_mul,hT j]
    by_cases hj : j = v
    · subst j
      simp [jointFlipSign,hv]
    · simp only [hj,ite_false,zero_mul]

end WaveTurbulence.VineEstS2
