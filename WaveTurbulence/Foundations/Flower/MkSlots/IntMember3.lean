/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntMember2
public import WaveTurbulence.Foundations.Flower.MkSlots.IntCapM

/-! # B3s MK-SLOTS (integration, member identity 3): the member's pinned skeleton value as a mode sum

The combined outer family of the α piece: B3's frontier-weighted family `fam₀` on the slots of `G_sb` that are not cap
pairs, one cap superposition `pc q` (from `CapSlotObligation`) on each cap pair `q` (`capFam`). For a member `y` of
the run class, its pinned skeleton value (`member_skelVal`) is the sum over the modes of the combined family of the
pinned outer values of `G_sb` (`outerValMμ` against `fixMeasure` of the piece's pins, decoration weight `ZwG`), with
`y`'s own unit kernels `unitRecenteredFW` (`member_hasSum`).

Route: the cap swap `skelValF_capSwap` (the member's cap slot kernels at the cap momentum are the representative's,
`member_capSlot`, i.e. the values of the cap superpositions) and `nonCap_slotFn_eq_slotFW` turn the member's pinned
slot family into the swapped B3 family `capSwap slotFW capFnY`; the pinned VINE-B♯ `hasSum_skelValF_outerValMμ` with
B3's regional bound (`memberRBMk`, `RegBound.capSwap`), B3's slot data on the non-cap slots (`memShape_slotFW`) and the
cap pieces on the cap slots; the pins and the unit interiors by R-core (`member_fixCap`, `member_fix_unit`), the unit
kernels by `unitKernelMG_capSwap` and B3's `member_ker_eqWMk`, the shape data by B3's `memShape_*`. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset TTree MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine WaveTurbulence.Flower.Stage1WNoVine
  WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.Flower.V5W

namespace WaveTurbulence.Flower.MkSlots.IntMember

open WaveTurbulence.Flower.MkSlots.IntRest WaveTurbulence.Flower.MkSlots.IntCore
  WaveTurbulence.Flower.MkSlots.IntCapM

/-! ### The combined family -/

section Fam
variable {w d : ℕ} {G : Garden w} (hG : G.IsPlain) (J : Finset (Fin w))

/-- The cap slots of `G_sb`. -/
def IsCapSlot (sl : ReplacementSlot G) : Prop := ∃ q, sl = Sum.inl q ∧ IsCapPair G hG J q

end Fam

/-! ### The member's mode sum -/

end WaveTurbulence.Flower.MkSlots.IntMember
