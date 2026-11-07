/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChartSourceAffineRows
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLNormalizedCoordinates

/-! # Exact row expressions appearing in frozen sumint hypothesis (iii) -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed

def sumintFormRowT {S : SumintShape} (T₁ T₂ : Matrix S.VIdx S.VIdx ℤ) :
    S.VIdx ⊕ S.VIdx ⊕ Fin 4 → S.VIdx → ℤ
  | .inl p => T₁ p
  | .inr (.inl v) => T₂ v
  | .inr (.inr _) => 0

def sumintFormRowH {S : SumintShape} (H₁ H₂ : S.VIdx → Fin 4 → ℤ) :
    S.VIdx ⊕ S.VIdx ⊕ Fin 4 → Fin 4 → ℤ
  | .inl p => H₁ p
  | .inr (.inl v) => H₂ v
  | .inr (.inr c) => Pi.single c 1

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

noncomputable def chartSourceFrozenTag (hM9 : VINEPARAM) (B : CLChainAssembly G R n) :
    CLChartSourceTag R → (assemblyShape hM9 B).VIdx ⊕ (assemblyShape hM9 B).VIdx ⊕ Fin 4
  | .inl (.inl p) => .inl (assemblyRowEquiv hM9 B p)
  | .inl (.inr v) => .inr (.inl (assemblyRowEquiv hM9 B v))
  | .inr j => .inr (.inr (if j = 0 then 2 else 3))

theorem formRowT_chartSourceTag (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (o : CLChartSourceTag R) :
    sumintFormRowT (assemblyPairMatrix hM9 B hG) (assemblyBranchMatrix hM9 B) (chartSourceFrozenTag hM9 B o) =
      sourceRowT hM9 B hG (chartSourceTag R o) := by
  rcases o with (p | v) | j <;> rfl

theorem formRowH_chartSourceTag (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (o : CLChartSourceTag R) :
    sumintFormRowH (assemblyPairBoundaryRow hM9 B hG) (assemblyBranchBoundaryRow hM9 B) (chartSourceFrozenTag hM9 B o) =
      sourceRowH hM9 B hG (chartSourceTag R o) := by
  rcases o with (p | v) | j <;> rfl

theorem normalized_formRowT (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (o : (assemblyShape hM9 B).VIdx ⊕ (assemblyShape hM9 B).VIdx ⊕ Fin 4)
    (j : (assemblyShape hM9 B).VIdx) :
    sumintFormRowT (normalizedPairMatrix hM9 B hG) (normalizedBranchMatrix hM9 B) o j =
      sumintFormRowT (assemblyPairMatrix hM9 B hG) (assemblyBranchMatrix hM9 B) o j * jointFlipSign _ j := by
  rcases o with p | v | c
  · rfl
  · rfl
  · exact (zero_mul _).symm

end WaveTurbulence.VineEstS2
