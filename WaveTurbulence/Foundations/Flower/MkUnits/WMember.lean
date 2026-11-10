/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnits.WAlign
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.Core1
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK5

/-! # MK-UNITS: the weighted member identity of a run class at a marking

Stage1WVine's `member_ker_eqW`, `memberRB`, `member_hVW`, `member_integW`, `member_hsmW` (main's VINE-B♯ member identity
with the frontier weight) for a member `y` of the run class `sourceClass a p kind mk`: its weighted value is the outer
mode sum of the representative's spliced garden at the marking, with the member's pinned unit kernels
`unitRecenteredFW`.  The gap selection uses B2c's `gapValue_eq_selDartsMk` (through main's `hZ_commonMk`), the
member's prescribed point uses `memberPoint_relatedMk`/`selPMk_iff_related` (`Code`).

Adapted from `Flower/Stage1WVine/WMember1.lean`, `WMember2.lean` (see `COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.MkUnits
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.VineC
  WaveTurbulence.LFTwist WaveTurbulence.VineAlign WaveTurbulence.Stage1 WaveTurbulence.RepAnalytic WaveTurbulence.VineA
  WaveTurbulence.Flower.Stage1WVine

variable {p : ℕ} {kind : Bool}

/-- B2c's dart-label gap identity at every garden, prescription and marking (B1b-3's hypothesis form). -/
theorem gapValueSelDartsMk_all (w : ℕ) : GapValueSelDartsMk w :=
  fun H τ _ _ L γ η base c κ hκ hc0 zsb hlab =>
    NormalizedSplice.gapValue_eq_selDartsMk (Mole.garden_isMolecule H) τ L γ η base c κ hκ hc0 zsb hlab

end WaveTurbulence.Flower.MkUnits
