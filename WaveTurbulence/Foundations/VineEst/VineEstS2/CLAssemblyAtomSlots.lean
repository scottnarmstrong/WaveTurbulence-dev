/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyAtoms
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyInputEquations

/-! # The global atom bijection restricts to each ingredient's own atom bijection -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

theorem assemblyAtomEquiv_input (hM9 : VINEPARAM)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) (i : Fin n) (j : Fin (assemblyChartAt hM9 B i).indexing.shape.n) :
    (assemblyAtomEquiv hM9 B ((assemblyInputEquiv hM9 B).symm ⟨i,j⟩)).1 =
      ((assemblyChartAt hM9 B i).indexing.atom j).1 := by
  induction B with
  | single hV R =>
    rw [assemblyInputEquiv_single_symm]
    rfl
  | append B hT hi hU R ih =>
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · rw [assemblyInputEquiv_append_zero_symm]
      rfl
    · exact ih i j

end WaveTurbulence.VineEstS2
