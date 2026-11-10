/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepUG3
public import WaveTurbulence.Foundations.Stage1.Represents.RepLfClk1
public import WaveTurbulence.Foundations.Stage1.Represents.RepUG5
public import WaveTurbulence.Foundations.Stage1.Represents.RepUG6
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

end WaveTurbulence.Represents
