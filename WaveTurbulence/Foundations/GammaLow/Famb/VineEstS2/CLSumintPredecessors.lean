/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.SumintLexEnumeration
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyShape
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLOrderedIdentity
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyRowEquiv
public import WaveTurbulence.Foundations.VineEst.VineEstS3.RowAlign
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintPredecessors
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.RowAlign
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintPredecessors` (sha256 1b21718f93ea49fe…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Actual regional predecessors in the frozen lexicographic row order -/

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

noncomputable def assemblyPrevΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (v : (assemblyShapeΓ hM9 B).VIdx) : Option (assemblyShapeΓ hM9 B).VIdx :=
  (clOrderedPrev B.isBlock R (assemblyIntOrderΓ hM9 B) ((assemblyRowEquivΓ hM9 B).symm v)).map (assemblyRowEquivΓ hM9 B)

theorem assemblyPrev_ltΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (v u : (assemblyShapeΓ hM9 B).VIdx) (h : assemblyPrevΓ hM9 B v = some u) :
    (assemblyShapeΓ hM9 B).LexLt u v := by
  obtain ⟨z,hz,rfl⟩ := Option.map_eq_some_iff.mp h
  have hl := assemblyRowEquiv_ltΓ hM9 B (clOrderedPrev_lt B.isBlock R (assemblyIntOrderΓ hM9 B) _ _ hz)
  simpa only [Equiv.apply_symm_apply] using hl

noncomputable def assemblyBudgetΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (v : (assemblyShapeΓ hM9 B).VIdx) : ℕ :=
  clOrderedBudget B.isBlock R (assemblyIntOrderΓ hM9 B) ((assemblyRowEquivΓ hM9 B).symm v)

theorem assemblyBudget_posΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n)
    (v : (assemblyShapeΓ hM9 B).VIdx) : 1 ≤ assemblyBudgetΓ hM9 B v :=
  clOrderedBudget_pos B.isBlock R (assemblyIntOrderΓ hM9 B) _

theorem prod_assemblyBudget_leΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) :
    (∏ v, assemblyBudgetΓ hM9 B v) ≤ 6561^(assemblyShapeΓ hM9 B).M := by
  rw [assemblyShape_MΓ]
  calc
    _ = ∏ v, clOrderedBudget B.isBlock R (assemblyIntOrderΓ hM9 B) v := (assemblyRowEquivΓ hM9 B).symm.prod_comp _
    _ ≤ _ := prod_clOrderedBudget_le B.isBlock R (assemblyIntOrderΓ hM9 B)

end WaveTurbulence.GammaLow.Famb.VineEstS2
