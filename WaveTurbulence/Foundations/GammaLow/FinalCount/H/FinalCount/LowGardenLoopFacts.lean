/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowGardenLoopFacts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenLift
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowIface3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowGardenLoopFacts`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **LOW-GARDEN (session 3): the combinatorics of loop atoms.**  A loop atom of `M` (`SubHypLoop R M`) carries exactly one loop, so
`M.deg v = M.unloop.deg v + 2` (`effDeg_eq_deg`) and `|loopAtoms M| = |loopBonds M|` (`card_loopAtoms_eq`). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.VineCount

section facts
variable {V : Type} [DecidableEq V] [Infinite V] {D : Type} [Fintype D] [DecidableEq D] {R : ℕ} {M : Molecule V D}

theorem effDeg_eq_deg (hS : SubHypLoop R M) {v : V} (hv : v ∈ M.atoms) : effDeg M v = M.deg v := by
  unfold effDeg
  by_cases hB : v ∈ loopAtoms M
  · obtain ⟨-, z, hz1, hz2⟩ := Finset.mem_filter.1 hB
    rw [if_pos hB, deg_loop_atom hS hv hz1 hz2]
  · rw [if_neg hB, add_zero]
    exact deg_unloop_eq M fun z hz hzl => hB (Finset.mem_filter.2 ⟨hv, z, hz, hzl⟩)

end facts
end WaveTurbulence.GammaLow.FinalCount.H
