/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepUG4
public import WaveTurbulence.Foundations.Stage1.Represents.RepUG5
public import WaveTurbulence.Foundations.Stage1.Represents.RepUG6
public import WaveTurbulence.Foundations.Stage1.Represents.RepLfClk2
import Mathlib.Tactic

/-!
# S2 REPRESENTS, UnitGap (7): hZ and the G2 clause of `outSet` for every decoration of `G_sb`

* `exists_ext_of_shape`: every decoration of `G_sb` extends to a decoration of the skeleton (interior local decorations exist
  for every balanced boundary: `exists_clLocalDecoration`, glued by `decSplit`).
* `hZ_stSt` (hZ, TARGET L1963): the literal spliced gap indicator at the restriction of a skeleton decoration is the indicator of
  the prescription restriction `selOf`.
* `unitGap_stSt` (G2, SG clause): for a decoration `z` of `G_sb` on which the literal spliced gap indicator does not vanish,
  every unit's boundary momenta `base + latticePoint L (z (hmom j i))` satisfy `UnitGap`.
* `mem_outSet_of_gsb` (G2): the `outSet` membership of `sumintBoundary` of those momenta, for any `SumintDatum` with
  `wBar = base` and `centre = sumintBoundary ζ (latPt ∘ c)`.
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

theorem exists_ext_of_shape (Φ : SpliceShape blk Gsb) (hS : S.IsPlain) (hd : Disj blk) {L : ℝ} (hL : L ≠ 0)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration Gsb d roots 0) :
    ∃ κ : GenDecoration S d roots 0, Φ.resDec hS hd κ = z := by
  classical
  have hb : ∀ j, Nonempty (CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) := by
    intro j
    have hbal := Φ.hmom_conservation hd j z.1 z.2.1
    have := exists_clLocalDecoration (blk j) L base (fun i => z.1 (Φ.hmom hd j i)) hbal
    rw [Φ.bdry_eq hd L base z.1 j]
    exact this
  refine ⟨(Φ.decSplit hS hd hL base roots).symm ⟨z, fun j => Classical.choice (hb j)⟩, ?_⟩
  have := (Φ.decSplit hS hd hL base roots).apply_symm_apply ⟨z, fun j => Classical.choice (hb j)⟩
  exact congrArg Sigma.fst this

open scoped Classical in
/-- **hZ.**  The literal spliced gap indicator at the restriction of a skeleton decoration is `[selOf σ]`. -/
theorem hZ_stSt (hM : S.molecule.IsMolecule) (hS : S.IsPlain) (σ : Prescription S) {L : ℝ} (hL : L ≠ 0) (γ η : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (κ : GenDecoration S d roots 0)
    (D : SplicedKernelData (stSt S σ).G d) (hD : D.gapSpecification = gapSpecification S σ) :
    splicedGapIndicator (stSt S σ).G D L γ η base
        ((stShape hM σ).resDec hS (unitBlk_disj hM σ) κ).1 =
      if selOf (GroupPrescription.ofPrescription σ) L γ η base κ.1 then 1 else 0 :=
  splicedGapIndicator_eq_selOf_gen hM hS σ hL γ η base roots κ _
    (fun y => bondIndex_stSt_od hM σ κ.1 y) D hD

open scoped Classical in
/-- **G2, SG clause, for every decoration of `G_sb`.** -/
theorem unitGap_stSt (hM : S.molecule.IsMolecule) (hS : S.IsPlain) (σ : Prescription S) {L : ℝ} (hL : L ≠ 0) (γ η : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration (stSt S σ).G d roots 0)
    (D : SplicedKernelData (stSt S σ).G d) (hD : D.gapSpecification = gapSpecification S σ)
    (hz : splicedGapIndicator (stSt S σ).G D L γ η base z.1 ≠ 0) (j : Fin (unitBlocks S σ).length) :
    VineB.UnitGap L γ η (fun i => base + latticePoint L (z.1 ((stShape hM σ).hmom (unitBlk_disj hM σ) j i))) := by
  classical
  obtain ⟨κ, hκ⟩ := exists_ext_of_shape (stShape hM σ) hS (unitBlk_disj hM σ) hL base roots z
  subst hκ
  have h1 := hZ_stSt hM hS σ hL γ η base roots κ D hD
  have hsel : selOf (GroupPrescription.ofPrescription σ) L γ η base κ.1 := by
    by_contra hn
    rw [if_neg hn] at h1
    exact hz h1
  have hu : unitBlk hM σ j ∈ unitBlocks S σ := List.get_mem _ _
  have hg := unitGap_of_selOf hM hS σ hL γ η base roots κ hsel hu
  have heq : ∀ i, ((stShape hM σ).resDec hS (unitBlk_disj hM σ) κ).1
      ((stShape hM σ).hmom (unitBlk_disj hM σ) j i) = κ.1 (bnodes (unitBlk hM σ j) i) := by
    intro i
    rw [SpliceShape.resDec_val]
    exact congrArg κ.1 ((stShape hM σ).node_hmom (unitBlk_disj hM σ) j i)
  simp only [heq]
  exact hg

open scoped Classical in
/-- **G2 (`outSet` membership) for every decoration of `G_sb` with non-vanishing literal gap indicator.** -/
theorem mem_outSet_of_gsb (hM : S.molecule.IsMolecule) (hS : S.IsPlain) (σ : Prescription S) {L : ℝ} (hL : L ≠ 0)
    (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration (stSt S σ).G d roots 0)
    (D : SplicedKernelData (stSt S σ).G d) (hD : D.gapSpecification = gapSpecification S σ)
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
    (unitGap_stSt hM hS σ hL γ η base roots z D hD hz j)
  refine ⟨fun c' => ⟨?_, ?_⟩, hcore.2, hg.1, hg.2⟩
  · rw [hw]; exact hcore.1 c'
  · rw [hct]
    exact sumintBoundary_close _ _ _ hball c'

end WaveTurbulence.Represents
