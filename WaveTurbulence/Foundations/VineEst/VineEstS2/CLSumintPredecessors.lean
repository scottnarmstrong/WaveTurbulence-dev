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

/-! # Actual regional predecessors in the frozen lexicographic row order -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open WaveTurbulence.VineEstS3
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

noncomputable def assemblyPrev (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (v : (assemblyShape hM9 B).VIdx) : Option (assemblyShape hM9 B).VIdx :=
  (clOrderedPrev B.isBlock R (assemblyIntOrder hM9 B) ((assemblyRowEquiv hM9 B).symm v)).map (assemblyRowEquiv hM9 B)

theorem assemblyPrev_lt (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (v u : (assemblyShape hM9 B).VIdx) (h : assemblyPrev hM9 B v = some u) :
    (assemblyShape hM9 B).LexLt u v := by
  obtain ⟨z,hz,rfl⟩ := Option.map_eq_some_iff.mp h
  have hl := assemblyRowEquiv_lt hM9 B (clOrderedPrev_lt B.isBlock R (assemblyIntOrder hM9 B) _ _ hz)
  simpa only [Equiv.apply_symm_apply] using hl

noncomputable def assemblyBudget (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (v : (assemblyShape hM9 B).VIdx) : ℕ :=
  clOrderedBudget B.isBlock R (assemblyIntOrder hM9 B) ((assemblyRowEquiv hM9 B).symm v)

theorem assemblyBudget_pos (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (v : (assemblyShape hM9 B).VIdx) : 1 ≤ assemblyBudget hM9 B v :=
  clOrderedBudget_pos B.isBlock R (assemblyIntOrder hM9 B) _

theorem prod_assemblyBudget_le (hM9 : VINEPARAM) (B : CLChainAssembly G R n) :
    (∏ v, assemblyBudget hM9 B v) ≤ 6561^(assemblyShape hM9 B).M := by
  rw [assemblyShape_M]
  calc
    _ = ∏ v, clOrderedBudget B.isBlock R (assemblyIntOrder hM9 B) v := (assemblyRowEquiv hM9 B).symm.prod_comp _
    _ ≤ _ := prod_clOrderedBudget_le B.isBlock R (assemblyIntOrder hM9 B)

end WaveTurbulence.VineEstS2
