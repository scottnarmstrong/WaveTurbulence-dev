/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintPredecessors
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLRegionalPredecessors
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLSumintPredecessors
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintRows` (sha256 1bd60f44703a0be5…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Source predecessor rows and coefficient counts on frozen sumint indices -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open WaveTurbulence.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS3
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

noncomputable def assemblyCoeffΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (v : (assemblyShapeΓ hM9 B).VIdx) : (assemblyShapeΓ hM9 B).VIdx ⊕ Fin 4 → ℤ
  | .inl p => clOrderedCoeff B.isBlock R hG (assemblyIntOrderΓ hM9 B) (assemblyPairOrderΓ hG B hM9) ((assemblyRowEquivΓ hM9 B).symm v)
      (.inl ((assemblyRowEquivΓ hM9 B).symm p))
  | .inr c => clOrderedCoeff B.isBlock R hG (assemblyIntOrderΓ hM9 B) (assemblyPairOrderΓ hG B hM9) ((assemblyRowEquivΓ hM9 B).symm v) (.inr c)

theorem assemblyCoeff_unitΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (v : (assemblyShapeΓ hM9 B).VIdx) (o : (assemblyShapeΓ hM9 B).VIdx ⊕ Fin 4) :
    IsUnitCoeff (assemblyCoeffΓ hM9 B hG v o) := by
  cases o with
  | inl p => exact clOrderedCoeff_unit B.isBlock R hG (assemblyIntOrderΓ hM9 B) (assemblyPairOrderΓ hG B hM9) _ (.inl ((assemblyRowEquivΓ hM9 B).symm p))
  | inr c => exact clOrderedCoeff_unit B.isBlock R hG (assemblyIntOrderΓ hM9 B) (assemblyPairOrderΓ hG B hM9) _ (.inr c)

open Classical in
theorem assemblyCoeff_count_leΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (v : (assemblyShapeΓ hM9 B).VIdx) :
    (Finset.univ.filter (fun p => assemblyCoeffΓ hM9 B hG v (.inl p) ≠ 0)).card +
    (Finset.univ.filter (fun c => assemblyCoeffΓ hM9 B hG v (.inr c) ≠ 0)).card ≤ assemblyBudgetΓ hM9 B v := by
  have he := Finset.card_equiv (assemblyRowEquivΓ hM9 B).symm
    (s := Finset.univ.filter (fun p => assemblyCoeffΓ hM9 B hG v (.inl p) ≠ 0))
    (t := Finset.univ.filter (fun p => clOrderedCoeff B.isBlock R hG (assemblyIntOrderΓ hM9 B) (assemblyPairOrderΓ hG B hM9)
      ((assemblyRowEquivΓ hM9 B).symm v) (.inl p) ≠ 0))
    (fun p => ⟨fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp h).2⟩,
      fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp h).2⟩⟩)
  rw [he]
  exact clOrdered_coeff_count_le B.isBlock R hG (assemblyIntOrderΓ hM9 B) (assemblyPairOrderΓ hG B hM9) _

noncomputable def assemblyBranchValueΓ {E : Type*} (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (κ : GNode G.tree → E) (v : (assemblyShapeΓ hM9 B).VIdx) : E :=
  clOrderedBranchValue B.isBlock R (assemblyIntOrderΓ hM9 B) κ ((assemblyRowEquivΓ hM9 B).symm v)

noncomputable def assemblyPairValueΓ {E : Type*} (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (hG : G.IsPlain) (κ : GNode G.tree → E) (v : (assemblyShapeΓ hM9 B).VIdx) : E :=
  clOrderedPairValue B.isBlock R hG (assemblyPairOrderΓ hG B hM9) κ ((assemblyRowEquivΓ hM9 B).symm v)

/-- The frozen row identity holds for actual regional source momenta;
conservation is required only on the original region. -/
theorem assembly_predecessor_identityΓ {E : Type*} [AddCommGroup E]
    (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain) (κ : GNode G.tree → E)
    (hκ : ∀ v : GBranch G.tree, v ∈ U → κ v.toNode = κ (v.child 0)-κ (v.child 1)+κ (v.child 2))
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode)
    (v : (assemblyShapeΓ hM9 B).VIdx) :
    assemblyBranchValueΓ hM9 B κ v - (assemblyPrevΓ hM9 B v).elim 0 (assemblyBranchValueΓ hM9 B κ) =
      (∑ p, assemblyCoeffΓ hM9 B hG v (.inl p) • assemblyPairValueΓ hM9 B hG κ p) +
      ∑ c, assemblyCoeffΓ hM9 B hG v (.inr c) • κ (clBoundaryNodes R c) := by
  have he : (assemblyPrevΓ hM9 B v).elim 0 (assemblyBranchValueΓ hM9 B κ) =
      (clOrderedPrev B.isBlock R (assemblyIntOrderΓ hM9 B) ((assemblyRowEquivΓ hM9 B).symm v)).elim 0 (clOrderedBranchValue B.isBlock R (assemblyIntOrderΓ hM9 B) κ) := by
    unfold assemblyPrevΓ
    cases hz : clOrderedPrev B.isBlock R (assemblyIntOrderΓ hM9 B) ((assemblyRowEquivΓ hM9 B).symm v) with
    | none => simp only [Option.map_none,Option.elim_none]
    | some z => simp only [Option.map_some,Option.elim_some,assemblyBranchValueΓ,Equiv.symm_apply_apply]
  rw [he]
  calc
    _ = _ := clOrdered_predecessor_identity_local B.isBlock R hG (assemblyIntOrderΓ hM9 B) (assemblyPairOrderΓ hG B hM9) κ hκ hp _
    _ = _ := by
      congr 1
      exact ((assemblyRowEquivΓ hM9 B).symm.sum_comp (fun p =>
        clOrderedCoeff B.isBlock R hG (assemblyIntOrderΓ hM9 B) (assemblyPairOrderΓ hG B hM9) ((assemblyRowEquivΓ hM9 B).symm v) (.inl p) •
          clOrderedPairValue B.isBlock R hG (assemblyPairOrderΓ hG B hM9) κ p)).symm

end WaveTurbulence.GammaLow.Famb.VineEstS2
