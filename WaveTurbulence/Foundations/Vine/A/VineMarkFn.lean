/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionPositions
/-! # B1a THREAD-ROOTS (ruling F-1): marked vine sets of a prime reconstruction, on main

Copied by source from `scope/B0-STAGE1MK/probe/Stage1MKProbe.lean` (sha256 `dab37b30…6c6b`): lines 9–26 (`AddrBelow`,
`ownRegion`, `nearRegion`, which `markedVinesRaw` uses) and lines 91–97 (`markedVinesRaw`, `MarkFn`), into the fresh
namespace `WaveTurbulence.Stage1Mk` (the world's `Flower.MkDefs` copies keep their own names until they switch to
these).  `MarkFn` is the type of the trailing marking argument `mk` of the prescribed-point roots (R12, default
`fun _ => ∅`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1Mk
open WaveTurbulence WaveTurbulence.LGSpine

variable {w : ℕ}

/-- A marking function: the marked vines of every prime reconstruction. -/
abbrev MarkFn (w : ℕ) := ∀ {LG : LayeredGarden w} (A : VineA.PrimeData LG), Set (Stage1.CLVine A.skeleton)

end WaveTurbulence.Stage1Mk
