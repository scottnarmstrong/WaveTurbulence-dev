/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Stage1.Represents.RepUG5
public import WaveTurbulence.Foundations.Stage1.Represents.RepUG6
/-! Actual decoration extension. Adapted from pinned/r83-RepUG7.lean;
original source SHA is in COPIED-SHA256SUMS. No selection premise is needed. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Stage1 RedSplice VineB RegRed Represents LGSpine
variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J]
  {blk : J → CLBlock S} {Gsb : Garden w}

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


/-- B1b (Mk-general form of `splice_labels_extend`). -/
theorem splice_labels_extendMk (hS : S.IsPlain) (σ : Prescription S) {L : ℝ} (hL : L ≠ 0)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) {Mk : Set (Stage1.CLVine _)} (z : GenDecoration (stSt (Mk := Mk) S σ).G d roots 0) :
    ∃ κ : GenDecoration S d roots 0, ∀ y,
      bondIndex (stSt (Mk := Mk) S σ).G z.1 y = bondIndex S κ.1 ((stSt (Mk := Mk) S σ).M.od y) := by
  obtain ⟨κ, hk⟩ := exists_ext_of_shape (stShape (Mk := Mk) (Mole.garden_isMolecule S) σ) hS
    (unitBlkMk_disj (Mk := Mk) (Mole.garden_isMolecule S) σ) hL base roots z
  refine ⟨κ, ?_⟩
  intro y
  rw [← hk]
  exact bondIndex_stSt_odMk (Mk := Mk) (Mole.garden_isMolecule S) σ κ.1 y

end WaveTurbulence.VineA
