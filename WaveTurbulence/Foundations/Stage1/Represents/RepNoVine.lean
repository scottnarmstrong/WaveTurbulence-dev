/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepGap
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproCross2
public import WaveTurbulence.Foundations.FinalCount.SubproSupportA
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

/-- B1b (Mk-general form of `stSt_eq_init_of_unitBlocks_empty`). -/
theorem stSt_eq_init_of_unitBlocks_emptyMk (σ : Prescription S) {Mk : Set (Stage1.CLVine _)} (h : unitBlocks (Mk := Mk) S σ = []) :
    stSt (Mk := Mk) S σ = SpState.init S := by
  unfold stSt; rw [h]; rfl

/-- B1b (Mk-general form of `stSt_G_eq_of_unitBlocks_empty`). -/
theorem stSt_G_eq_of_unitBlocks_emptyMk (σ : Prescription S) {Mk : Set (Stage1.CLVine _)} (h : unitBlocks (Mk := Mk) S σ = []) :
    (stSt (Mk := Mk) S σ).G = S := by
  rw [stSt_eq_init_of_unitBlocks_emptyMk (Mk := Mk) σ h]; rfl

/-- `G_sb = G_sk` when no unit is spliced. -/
theorem stSt_G_eq_of_unitBlocks_empty (σ : Prescription S) (h : unitBlocks S σ = []) :
    (stSt S σ).G = S := stSt_G_eq_of_unitBlocks_emptyMk (Mk := ∅) σ h

/-- B1b (Mk-general form of `stSt_hinges_eq_empty`). -/
theorem stSt_hinges_eq_emptyMk (σ : Prescription S) {Mk : Set (Stage1.CLVine _)} (h : unitBlocks (Mk := Mk) S σ = []) :
    (stSt (Mk := Mk) S σ).hinges = ∅ := by
  classical
  ext c
  simp only [SpState.mem_hinges, Finset.notMem_empty, iff_false, not_not]
  have hs := stSt_eq_init_of_unitBlocks_emptyMk (Mk := Mk) σ h
  have : ∀ st : SpState S, st = SpState.init S → ∀ c : GBranch st.G.tree, st.cls (st.M.ob c) = none := by
    rintro st rfl c; rfl
  exact this _ hs c

/-- No hinges when no unit is spliced. -/
theorem stSt_hinges_eq_empty (σ : Prescription S) (h : unitBlocks S σ = []) :
    (stSt S σ).hinges = ∅ := stSt_hinges_eq_emptyMk (Mk := ∅) σ h

end WaveTurbulence.Represents
