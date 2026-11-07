/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.SumintLexEnumeration
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyShape
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLOrderedRows

/-! # The frozen lexicographic row order of an assembly (split from `CLSumintPredecessors`) -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

noncomputable def assemblyRowEquiv (hM9 : VINEPARAM) (B : CLChainAssembly G R n) :
    Fin (clLocalOrder1 R) ≃ (assemblyShape hM9 B).VIdx :=
  (finCongr (assemblyShape_M hM9 B).symm).trans (sumintRowEnumeration _)

theorem assemblyRowEquiv_lt (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    {i j : Fin (clLocalOrder1 R)} (h : i < j) :
    (assemblyShape hM9 B).LexLt (assemblyRowEquiv hM9 B i) (assemblyRowEquiv hM9 B j) :=
  sumintRowEnumeration_lt _ h

/-- Converse of `assemblyRowEquiv_lt`: the lexicographic order on rows is the order of the enumeration. -/
theorem assemblyRowEquiv_symm_lt (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    {x y : (assemblyShape hM9 B).VIdx} (h : (assemblyShape hM9 B).LexLt x y) :
    (assemblyRowEquiv hM9 B).symm x < (assemblyRowEquiv hM9 B).symm y := by
  by_contra hc
  rcases (not_lt.mp hc).lt_or_eq with hlt | heq
  · have h2 := assemblyRowEquiv_lt hM9 B hlt
    simp only [Equiv.apply_symm_apply] at h2
    rcases h with h | ⟨h1, h3⟩ <;> rcases h2 with h2 | ⟨h4, h5⟩
    · exact absurd h (not_lt.mpr h2.le)
    · exact absurd h4 (ne_of_gt h)
    · exact absurd h1 (ne_of_gt h2)
    · omega
  · have := (assemblyRowEquiv hM9 B).symm.injective heq
    subst this
    rcases h with h | ⟨_, h⟩ <;> omega

end WaveTurbulence.VineEstS2
