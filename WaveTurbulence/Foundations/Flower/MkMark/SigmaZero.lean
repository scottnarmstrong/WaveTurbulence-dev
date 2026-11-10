/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.SigmaBridge
public import WaveTurbulence.Foundations.Flower.MkMark.SigmaCrown

/-! # B2b-3 MK-MARK (c): zero weight for stem-unclean pairs under main's σ-restriction

`weight_zero_of_unclean` (StemZero) needs, on the selection, a crown gap `‖k(u₂₁) − k(u₂₂)‖ < ‖k_root‖/2` at the
lower joint `u₂` of the core vine. Here it is derived from main's σ-restriction on the collapsed skeleton decoration:

* `weight_zero_of_unclean_vinesV0`: the selection carries a skeleton integer decoration `z` with
  `selOf (ofPrescription σ) L γ η base z` and `skDec A k = k₀ + z/L`; the core vine `u` is (the atom set of) a vine of
  `vinesV0 A.skeleton σ`; the root is high, `L^{-γ+η} < ‖k_root‖/2`.
* `weight_zero_of_unclean_collapsed`: the same with `z` the collapse (`collapseGenDecoration`) of an integer
  decoration `κ` of the decoded garden and `k = k₀ + κ/L` — the form in which main's Stage-1 selections are stated. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton
  WaveTurbulence.RegRed WaveTurbulence.RedSplice

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

/-- The skeleton reading of a coset decoration of the decoded garden is the coset decoration of the collapse. -/
theorem skDec_coset_collapse {LG : LayeredGarden w} (A : VineA.PrimeData LG) {d : ℕ} {n : Fin w → (Fin d → ℤ)}
    {nfl : Fin d → ℤ} (κ : GenDecoration (A.data.garden A.prime.1) d n nfl) (L : ℝ) (k₀ : Mom d)
    (k : GNode LG.garden.tree → Mom d) (hk : ∀ x, k x = k₀ + latticePoint L (ofForest A κ.1 x)) :
    skDec A k = cosetDecoration A.skeleton L k₀ (collapseGenDecoration A.data A.prime.1 κ).1 := by
  funext a
  have h1 := collapseGenDecoration_skDec A κ a
  show k _ = k₀ + latticePoint L _
  rw [h1]
  exact hk _

end WaveTurbulence.Flower.MkMark
