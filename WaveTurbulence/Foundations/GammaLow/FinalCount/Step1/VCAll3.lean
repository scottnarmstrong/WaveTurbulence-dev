/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCAll3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAll2
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VCAll3`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 # VINE-COUNT part 32: **Prop 9.4, Step 1, for every vine-like object removed by `Stage2Op.vine`** (DH23 L1773--L1801).

The VC removed in Step 1 is, by `Prop subsetvc` (L1797: "`𝕍ℂ` is either a single vine, or is formed by two double bonds"),
a single vine (an ordinary VC, or the adjoint of a hyper object: HV and the triple bonds of `subpro` (c)) or two double
bonds `a = x = b` (`DoubleShape`; a VC, or the adjoint of an HVC).  `prop94_vine_all` proves the deviation bound in each
case, with a chart (`Charted`; main: `VINEPARAM`) the only vine hypothesis.  NOT covered, and false as a count: a chain of `m ≥ 2` vines that is not
two double bonds (see `FINDING-CHAIN` in `PROGRESS.md`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount hiding latticePoint_injective latticePoint_sub mem_ladderAtoms
open WaveTurbulence.VineCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.CountLemmas

variable {d : ℕ}

/-- The removed VC of `K` is a single vine: of `M` for an ordinary VC, of the adjoint `eraseBond M R.added` for a
hyper object (DH23 L1797, first alternative of `Prop subsetvc`). -/
def SingleVineVC {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    (K : VineCut g M) : Prop :=
  match K.C.shape with
  | .vc _ => Charted M K.C.atoms K.C.upper K.C.lower
  | .hyper R => Charted (Molecule.eraseBond M R.added) K.C.atoms K.C.upper K.C.lower

end WaveTurbulence.GammaLow.FinalCount.Step1
