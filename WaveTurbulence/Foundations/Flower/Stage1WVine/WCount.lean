/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.WSlotData
public import WaveTurbulence.Foundations.Stage1.Represents.RepVB17

/-! # STAGE1W-VINE (T6, part 4): the frontier weight budget of a vine piece

`weight_exponent_le`: the `cψ`-exponents of a vine piece add up to at most
`3 · |reconstruction| + 9 · |S| + 4 · n`: the outer slots carry `cψ ^ slotNr` (at most all garden-nonroot nodes,
O4′'s `sum_slotNr`), unit `j` carries `cψ ^ (9 |U_j| + 4 n₂(j))` (the staged `V5FrontierClassBoundAt`), the atom sets of
the units are disjoint, and `Σ_j n₂(j) ≤ n` (main's `exponent_order`).  With `|reconstruction| = N`, `|S| ≤ N`, `n = N`
this is the R151 budget `16 N`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.Stage1WVine
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Represents

variable {w : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

theorem weight_exponent_le (Φ : SpliceShape blk Gsb) (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain)
    (hSb : Gsb.IsPlain) (n : ℕ) (hn : n - S.order = D.size) (hnS : S.order ≤ n) :
    (∑ s', Stage1WNoVine.slotNr D hS (Φ.iota hS hSb s')) +
        ∑ j, (9 * (blk j).atoms.card + 4 * clLocalOrder2 D hS (regionOf (blk j))) ≤
      3 * (D.garden hS).order + 9 * S.order + 4 * n := by
  have h1 : ∑ s', Stage1WNoVine.slotNr D hS (Φ.iota hS hSb s') ≤ 3 * (D.garden hS).order := by
    rw [← Stage1WNoVine.sum_slotNr D hS]
    calc ∑ s', Stage1WNoVine.slotNr D hS (Φ.iota hS hSb s')
        = ∑ s ∈ Finset.univ.image (Φ.iota hS hSb), Stage1WNoVine.slotNr D hS s :=
          (Finset.sum_image fun x _ y _ h => Φ.iota_inj hS hSb h).symm
      _ ≤ ∑ s, Stage1WNoVine.slotNr D hS s := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have h2 : ∑ j, (blk j).atoms.card ≤ S.order := by
    rw [← Finset.card_biUnion (fun x _ y _ hxy => hd x y hxy)]
    calc _ ≤ Fintype.card (GBranch S.tree) := Finset.card_le_univ _
      _ = S.order := WaveTurbulence.Mole.card_gbranch S.tree
  have h3 := exponent_order Φ hd D hS hSb n hn hnS
  have h4 : ∑ j, clLocalOrder2 D hS (regionOf (blk j)) ≤ n := by omega
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  omega

end WaveTurbulence.Flower.Stage1WVine
