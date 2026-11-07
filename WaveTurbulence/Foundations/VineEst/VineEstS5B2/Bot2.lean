/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot1

/-! # V5 Step 4d-B2: the bottom vine, part 2 (the geometry of the whole chain region at a twist of the bottom piece)

For a chain region `c` of a core family `F` whose bottom joint is the lower joint of the member `i`, the region data of `c` has kept slot
`(placement i).keep` (`chain_slow`), so `SLow` holds for `S = c.U`; the region data of the transported chain `c.next i true` has the same kept
slot, so `STw` holds (`chain_stw`).  Together with the explicit slots of the boundary children (`freeSwap`) this is the geometry
of the twist of the bottom vine.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {ι : Type*}

theorem chain_slow {S : Garden w} {F : CoreFamily S ι} (c : ChainAt S F) (i : ι) (hb : c.b = (F.placement i).lower) :
    SLow (F.placement i) (clRegionData S c.block c.cl) := by
  refine ⟨c.block, hb, ?_⟩
  have h1 : (F.placement i).keep.succ ∈ Mole.internalPositions S c.U (F.placement i).lower :=
    internalPositions_mono S (c.atoms_sub i) _ (((F.designated i).2 (F.placement i).keep).mpr rfl)
  have h2 := ((clRegionData S c.block c.cl).lower (F.placement i).keep).mp (by rw [hb]; exact h1)
  exact h2.symm

theorem chain_stw {S : Garden w} {F : CoreFamily S ι} (c : ChainAt S F) (i : ι) (hb : c.b = (F.placement i).lower) :
    STw (F.placement i) (clRegionData S c.block c.cl)
      (clRegionData (chosenSkeleton S (F.placement i) true) (c.next i true).block (c.next i true).cl) := by
  have h1 := chain_slow c i hb
  have hb' : (c.next i true).b = ((nextFam F i true).placement i).lower := by
    show coreBranchEquiv S (F.placement i) c.b = (F.nextPlacement i i).lower
    rw [F.nextPlacement_lower, hb]
  have h2 := chain_slow (c.next i true) i hb'
  refine ⟨h1.block, h1.lower, h1.keep, ?_⟩
  exact h2.keep.trans (F.nextPlacement_keep i i)

end WaveTurbulence.VineEstS5B2
