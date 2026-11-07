/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepNU4
public import WaveTurbulence.Foundations.Stage1.Represents.RepUG7
import Mathlib.Tactic

/-!
# S2 REPRESENTS, UnitGap (7), R83 successor

`hZ_stStN`, `unitGap_stStN`, `mem_outSet_of_gsbN`: `hZ_stSt`, `unitGap_stSt`, `mem_outSet_of_gsb` against the successor
`NormalizedSplice.gapSpecification` / `selOf` (the G2 glue; `exists_ext_of_shape` of `RepUG7` is designation-free and reused).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Represents
open Finset TTree WaveTurbulence WaveTurbulence.Mole WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS2 WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3.Eng

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

open scoped Classical in
/-- **hZ.**  The literal spliced gap indicator at the restriction of a skeleton decoration is `[selOf σ]`. -/
theorem hZ_stStN (hM : S.molecule.IsMolecule) (hS : S.IsPlain) (σ : Prescription S) {L : ℝ} (hL : L ≠ 0) (γ η : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (κ : GenDecoration S d roots 0)
    (D : SplicedKernelData (stSt S σ).G d) (hD : D.gapSpecification = VineA.NormalizedSplice.gapSpecification S σ) :
    splicedGapIndicator (stSt S σ).G D L γ η base
        ((stShape hM σ).resDec hS (unitBlk_disj hM σ) κ).1 =
      if VineA.NormalizedSplice.selOf (VineA.NormalizedSplice.GroupPrescription.ofPrescription σ) L γ η base κ.1 then 1 else 0 :=
  VineA.NormalizedSplice.splicedGapIndicator_eq_selOf_gen hM hS σ hL γ η base roots κ _
    (fun y => bondIndex_stSt_od hM σ κ.1 y) D hD

open scoped Classical in
/-- **G2, SG clause, for every decoration of `G_sb`.** -/
theorem unitGap_stStN (hM : S.molecule.IsMolecule) (hS : S.IsPlain) (σ : Prescription S) {L : ℝ} (hL : L ≠ 0) (γ η : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration (stSt S σ).G d roots 0)
    (D : SplicedKernelData (stSt S σ).G d) (hD : D.gapSpecification = VineA.NormalizedSplice.gapSpecification S σ)
    (hz : splicedGapIndicator (stSt S σ).G D L γ η base z.1 ≠ 0) (j : Fin (unitBlocks S σ).length) :
    VineB.UnitGap L γ η (fun i => base + latticePoint L (z.1 ((stShape hM σ).hmom (unitBlk_disj hM σ) j i))) := by
  classical
  obtain ⟨κ, hκ⟩ := exists_ext_of_shape (stShape hM σ) hS (unitBlk_disj hM σ) hL base roots z
  subst hκ
  have h1 := hZ_stStN hM hS σ hL γ η base roots κ D hD
  have hsel : VineA.NormalizedSplice.selOf (VineA.NormalizedSplice.GroupPrescription.ofPrescription σ) L γ η base κ.1 := by
    by_contra hn
    rw [if_neg hn] at h1
    exact hz h1
  have hu : unitBlk hM σ j ∈ unitBlocks S σ := List.get_mem _ _
  have hg := unitGap_of_selOfN hM hS σ hL γ η base roots κ hsel hu
  have heq : ∀ i, ((stShape hM σ).resDec hS (unitBlk_disj hM σ) κ).1
      ((stShape hM σ).hmom (unitBlk_disj hM σ) j i) = κ.1 (bnodes (unitBlk hM σ j) i) := by
    intro i
    rw [SpliceShape.resDec_val]
    exact congrArg κ.1 ((stShape hM σ).node_hmom (unitBlk_disj hM σ) j i)
  simp only [heq]
  exact hg

open scoped Classical in
/-- **G2 (`outSet` membership) for every decoration of `G_sb` with non-vanishing literal gap indicator.** -/
theorem mem_outSet_of_gsbN (hM : S.molecule.IsMolecule) (hS : S.IsPlain) (σ : Prescription S) {L : ℝ} (hL : L ≠ 0)
    (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration (stSt S σ).G d roots 0)
    (D : SplicedKernelData (stSt S σ).G d) (hD : D.gapSpecification = VineA.NormalizedSplice.gapSpecification S σ)
    (hz : splicedGapIndicator (stSt S σ).G D L γ η base z.1 ≠ 0) (j : Fin (unitBlocks S σ).length)
    (c : Fin 4 → Fin d → ℤ)
    (hball : ∀ i, ‖(base + latticePoint L (z.1 ((stShape hM σ).hmom (unitBlk_disj hM σ) j i))) - latPt d (c i)‖ ≤ 1)
    (DS : SumintDatum d) (hw : DS.wBar = base)
    (hct : DS.centre = sumintBoundary (S.sign (unitBlk hM σ j).upper.toNode) (fun i => latPt d (c i))) :
    sumintBoundary (S.sign (unitBlk hM σ j).upper.toNode)
        (fun i => base + latticePoint L (z.1 ((stShape hM σ).hmom (unitBlk_disj hM σ) j i))) ∈ outSet DS L γ η := by
  have hcore := (stShape hM σ).hmom_outSet_core (unitBlk_disj hM σ) j L base z.1 z.2.1
  have hg := (sumintBoundary_gap_iff (S.sign (unitBlk hM σ j).upper.toNode) L γ η
    (fun i => base + latticePoint L (z.1 ((stShape hM σ).hmom (unitBlk_disj hM σ) j i)))).mpr
    (unitGap_stStN hM hS σ hL γ η base roots z D hD hz j)
  refine ⟨fun c' => ⟨?_, ?_⟩, hcore.2, hg.1, hg.2⟩
  · rw [hw]; exact hcore.1 c'
  · rw [hct]
    exact sumintBoundary_close _ _ _ hball c'

end WaveTurbulence.Represents
