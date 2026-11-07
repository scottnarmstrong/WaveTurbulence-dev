/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVD6
public import WaveTurbulence.Foundations.Stage1.Represents.RepVD2
public import WaveTurbulence.Foundations.Stage1.Represents.RepVD3
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 12: the member identity `hV` of the class sum (B3)

`selSkC`: the common selection `gap.value = 1` on the decorations of `G_sb`.
`valueSel_selAt_reconstruction`: reading the selection of a prescribed point at the reconstruction of its data.
`member_hV`: for a member `y` of the unit class, the value `U.toLF.valueSel (selP π)` is the outer mode sum with the common
data of the representative and the member's unit kernels `unitRecenteredW`.
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

variable {w p : ℕ} {kind : Bool}

/-- The common selection of `G_sb`: the class gap functional is `1`. -/
def selSkC {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) {d : ℕ} (L γ η : ℝ) (hL : L ≠ 0) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) (z : GenDecoration a.fullProfile.piece.gap.garden d roots 0) : Prop :=
  a.fullProfile.piece.gap.value d L γ η hL base roots z = 1

open scoped Classical in
theorem selSkC_ite {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) {d : ℕ} (L γ η : ℝ) (hL : L ≠ 0) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) (z : GenDecoration a.fullProfile.piece.gap.garden d roots 0) :
    a.fullProfile.piece.gap.value d L γ η hL base roots z = if selSkC a L γ η hL base roots z then 1 else 0 := by
  rcases gap_value_01 a hL γ η base roots z with h | h
  · rw [if_neg (by unfold selSkC; rw [h]; norm_num), h]
  · rw [if_pos (by unfold selSkC; exact h), h]

open scoped Classical in
theorem valueSel_selAt_reconstruction {P : WTParams} {S : Garden w} (F : LeafFamily P w) (D : ReconstructionData S)
    (hprime : IsPrimeGarden S) (layer : GNode (D.forest hprime.1) → ℕ) (hLayer : IsLayering (D.garden hprime.1) layer)
    (LG : LayeredGarden w) (hspec : layeredReconstruction D hprime.1 layer hLayer = LG)
    (hd : D.Decodes hprime.1 LG.garden) (σ : NormalizedSplice.GroupPrescription S) (tt : Fin w → ℝ) (base : Mom P.d)
    (roots : Fin w → (Fin P.d → ℤ)) :
    F.valueSel tt base roots LG (fun κ => selAt P base ⟨S, hprime, D, hd⟩ σ κ) =
      F.valueSel tt base roots (layeredReconstruction D hprime.1 layer hLayer)
        (fun κ => NormalizedSplice.selOf σ P.L P.γ P.η base (collapseGenDecoration D hprime.1 κ).1) := by
  subst hspec
  rfl


theorem sourceClass_mem_outputs {R : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind) :
    y.1.layered ∈ a.outputs (p := p) (kind := kind) := by
  obtain ⟨M, hM, hr⟩ := member_trace a y hy
  rw [prescribed_outputs_eq_unitsStart a (sourceLayer a) (sourceLayer_isLayering a) (sourceLayer_reconstructs a)]
  exact ⟨M, y.1, hM, hr.batch, rfl⟩

open PrescribedPrimeGarden in
theorem memberPoint_related' {R : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind)
    (M : List (UnitsIndex (sourceAssembly a)))
    (hr : ReachU p kind (unitsSplit (sourceAssembly a)).Q M (sourceStart a) (sourceUnits a) y.1 y.2) :
    Related (p := p) (kind := kind) a (memberPoint a y M hr) := by
  have hmem := sourceClass_mem_outputs a y hy
  obtain ⟨c, hc, hce⟩ := (Set.ext_iff.mp (tauClass_image a) y.1.layered).mpr hmem
  have hcode : c.code = (memberPoint a y M hr).code :=
    (Related.code_eq hc).symm.trans (memberPoint_code a y M hr).symm
  have : c = memberPoint a y M hr := eq_of_layered_code hce hcode
  rw [← this]
  exact hc

theorem sourceShape_data {R : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind) :
    ∃ (M : List (UnitsIndex (sourceAssembly a)))
      (hr : ReachU p kind (unitsSplit (sourceAssembly a)).Q M (sourceStart a) (sourceUnits a) y.1 y.2)
      (hn : M.Nodup), sourceShape a y hy = commonShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma
        a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) hr hn := by
  obtain ⟨hn, hr⟩ := (class_member_trace (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy).choose_spec
  exact ⟨_, hr, hn, rfl⟩

end WaveTurbulence.Represents
