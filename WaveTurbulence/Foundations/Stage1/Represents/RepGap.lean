/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.FinalCount.RedSpliceGapKind
public import WaveTurbulence.Foundations.Spine.SourceBlockJointGaps
public import WaveTurbulence.Foundations.Spine.GardenDegreeFourSource
public import WaveTurbulence.Foundations.Spine.SplicedMoleculeDecoration
import Mathlib.Tactic

/-!
# S2 REPRESENTS, W1b: the spliced gap indicator is the `σ`-restriction

Restriction direction (no lift): for a conserving decoration `z` of the original garden `G` and ANY
labels `κsb = κ ∘ od` of `G_sb`, `splicedGapIndicator G_sb = [selOf σ z]` (TARGET L1950, L1956).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
  WaveTurbulence.RedSplice

variable {w : ℕ} {G : Garden w}

/-- Every vine-like object has a gap (at its upper joint) for any labels. -/
theorem exists_hasGapKind {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} (O : SourceVine.Object M) {d : ℕ} (L γ η : ℝ) (v : Mom d)
    (κ : D → (Fin d → ℤ)) : ∃ k, O.HasGapKind L γ η v κ k := by
  classical
  cases hs : O.shape with
  | vc hv =>
    obtain ⟨r, hr⟩ := source_block_joint_gap_exists M hv.1 (Or.inl rfl) L v κ
    refine ⟨_, r, ?_, rfl⟩
    unfold SourceVine.VineLikeObject.IsGap
    rw [hs]; exact hr
  | hyper R =>
    obtain ⟨r, hr⟩ := source_block_joint_gap_exists (Mole.eraseBond M R.added) R.adjoint.1 (Or.inl rfl)
      L v (fun x => κ x.1)
    refine ⟨_, r, ?_, rfl⟩
    unfold SourceVine.VineLikeObject.IsGap
    rw [hs]; exact hr


end WaveTurbulence.Represents
