/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepGap
public import WaveTurbulence.Foundations.Stage1.Represents.RepGlue
import Mathlib.Tactic

/-!
# S2 REPRESENTS, vine-free case, step 1: no unit is spliced, so `G_sb = G_sk`

If `unitBlocks S σ = []` (no SG vine chain in `𝒱₀`), then `stSt S σ` is the trivial splice `SpState.init S`:
`G_sb = S`, no hinges, the old-name maps are the identity, the inherited pre-layering is the pre-layering.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.LGSpine WaveTurbulence.RedSplice

variable {w : ℕ} {S : Garden w}

theorem stSt_eq_init_of_unitBlocks_empty (σ : Prescription S) (h : unitBlocks S σ = []) :
    stSt S σ = SpState.init S := by
  unfold stSt; rw [h]; rfl

/-- `G_sb = G_sk` when no unit is spliced. -/
theorem stSt_G_eq_of_unitBlocks_empty (σ : Prescription S) (h : unitBlocks S σ = []) :
    (stSt S σ).G = S := by
  rw [stSt_eq_init_of_unitBlocks_empty σ h]; rfl

/-- No hinges when no unit is spliced. -/
theorem stSt_hinges_eq_empty (σ : Prescription S) (h : unitBlocks S σ = []) :
    (stSt S σ).hinges = ∅ := by
  classical
  ext c
  simp only [SpState.mem_hinges, Finset.notMem_empty, iff_false, not_not]
  have hs := stSt_eq_init_of_unitBlocks_empty σ h
  have : ∀ st : SpState S, st = SpState.init S → ∀ c : GBranch st.G.tree, st.cls (st.M.ob c) = none := by
    rintro st rfl c; rfl
  exact this _ hs c

end WaveTurbulence.Represents
