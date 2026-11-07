/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp18Comb
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp16Main
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Class

/-! # The split of the start chain region at a member (V5 Step 4b, step 4, WP-D)

`exists_assemblySplit`: for a chain assembly `B`, a core member `pstar` that is not the bottom piece (`1 ≤ pstar.1`) there is a
`SplitAt` of the start chain region `chainStart B` with `J` the members below `pstar` (TARGET (tildeJ2): `U^{≥p}` and `U^{<p}`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open Finset RegRed TTree WaveTurbulence WaveTurbulence.Twist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
variable {w : ℕ} {G : Garden w}
  {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}

/-- The members of the assembly family strictly below `pstar` (the lower block). -/
def belowSet (B : CLChainAssembly G R n) (pstar : (assemblySourceFamily B).CoreIndex) :
    Set (assemblySourceFamily B).CoreIndex := {j | j.1.val < pstar.1.val}

theorem exists_assemblySplit (B : CLChainAssembly G R n) (pstar : (assemblySourceFamily B).CoreIndex)
    (hk : 1 ≤ pstar.1.val) :
    ∃ sp : SplitAt G (assemblySourceFamily B).coreFamily pstar (belowSet B pstar), sp.c = chainStart B := by
  obtain ⟨Sk, Tk, bk, hSk, hTk, hint, hun, hat1, hat2, hlow, hne⟩ :=
    exists_split_assembly B pstar.1.val hk pstar.1.2
  have hU : G.molecule.IsBlock (Sk ∪ Tk) a b := hun ▸ B.isBlock
  have hTb : G.molecule.IsBlock Tk bk b := chain_suffix_currentBlock G.molecule (Mole.garden_isMolecule G) hSk hTk hint hU
  have hpl : (assemblySourceFamily B).lower pstar.1 = bk := hlow pstar.1.2
  have hpl' : ((assemblySourceFamily B).coreFamily.placement pstar).lower = bk := by
    have h1 := ((assemblySourceFamily B).corePlacement_at pstar).1
    exact h1.trans hpl
  refine ⟨{ c := chainStart B
            sb := ⟨Sk, a, bk, hSk⟩
            tb := ⟨Tk, bk, b, hTb⟩
            sa := rfl
            tbb := rfl
            joint := rfl
            bk := hpl'.symm
            inter := hint
            union := hun.symm
            atomsJ := ?_
            lowJ := ?_ }, rfl⟩
  · intro j hj
    exact hat1 j.1 hj
  · intro j hj
    have h1 := ((assemblySourceFamily B).corePlacement_at j).1
    change ((assemblySourceFamily B).corePlacement j).lower ≠ bk
    rw [h1]
    exact hne j.1 hj

end WaveTurbulence.VineEstS4
