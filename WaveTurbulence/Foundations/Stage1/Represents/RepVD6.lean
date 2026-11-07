/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVD5
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 12: the per-member outer slot data are the representative's

For a class member `y` of the unit class of the representative `a`, the outer data of `valueSel_modes` (layer, hinges, route,
clocks, boundary nodes, unit kernel profile) are those of `a` (`member_lay_eq`, `member_ker_eq`, VINE-ALIGN's exports).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic MeasureTheory

variable {p : ℕ} {kind : Bool}

theorem member_lay_eq {R : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind) :
    (fun c => stateLayer y.1 (y.1.data.coreBranch y.1.plain ((sourceShape a y hy).br c)).toNode) =
      a.fullProfile.piece.layer :=
  funext (sourceShape_core_layer a y hy)

theorem member_ker_eq {R d : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind) (L γ δ : ℝ)
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (base : Mom d) :
    unitKernelM (fun j => unitClBlock (y.2 j)) y.1.data y.1.plain L γ δ h (stateLayer y.1) (stateLayer_isLayering y.1)
        base =
      fun (j : Fin (unitBlocks a.prime.skeleton a.totalSigma).length) (lam : ℤ) (t : Fin 3 → ℝ) (k : Fin 4 → Mom d) =>
        unitRecenteredW y.1 (y.2 j) L γ δ
        (unitProfile (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) h j) base (modW lam)
        (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3) := by
  funext j lam t k
  rw [unitKernelM_eq_unitRecenteredW y.1 y.2 (stateLayer y.1) (stateLayer_isLayering y.1) (stateLayer_spec y.1)]
  have hidx := source_upper_tree_index a y hy j
  have : unitProfile (fun j => unitClBlock (y.2 j)) h j =
      unitProfile (unitBlk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) h j := by
    funext q
    unfold unitProfile
    exact congrArg₂ (fun u v => h q u v) hidx hidx
  rw [this]

end WaveTurbulence.Represents
