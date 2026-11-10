/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VrHyper3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3TVineRho
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.VrHyper3`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # VINE-RHO (8): the `ρ`-loss of vine chains, hyper objects and DV's (TARGET L2226, Operation 1)

All statements are for the universe's object definitions (`WaveTurbulence.LGSpine.SourceVine`: `Chain`, `IsVC`, `IsHV`,
`IsHVC`, `IsDV`).  A chain of `n` vines costs at most `42 n` (`chain_ladderLoss_le`); an HV costs `42`; an HVC with `n` ingredients
costs `42 n`; a DV costs `84`.  The loss genuinely grows with `n` (see PROGRESS.md: a chain of `n` double bonds).

Low-range change (L6-HG3): the objects are those of the low family (`Src … Src.γL`); the vine bound is
`someVine_ladderLoss_le_of_agree` (`G3TVineRho`: main's bound for (I), (II), L3's N3 Thm 6 (iv) for T-vines), so the
statements take the layer's named input `[Src.G3Inputs V D]` (`H/InputsG3.lean`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.VineRho
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountAsm Finset
set_option linter.unusedSectionVars false
universe u1 u2 u3
variable {V : Type u1} [DecidableEq V] {D : Type u2} [Fintype D] [DecidableEq D] {D' : Type u3} [Fintype D'] [DecidableEq D']

/-- **HV**: the adjoint of a single vine costs at most `42`. -/
theorem hv_ladderLoss_le [Src.G3Inputs V D] (M : Molecule V D) (hM : M.IsMolecule) {S : Finset V} {a b : V} (h : Src.IsHV Src.γL M S a b) :
    ladderLoss M (M.atoms \ S) ≤ 42 := by
  obtain ⟨e, he, hX⟩ := h
  have hM' := eraseBond_isMolecule_of_ends M hM e hX.block.2.2.2.1 he
  exact someVine_ladderLoss_le_of_agree M hM _ hM' (agree_eraseBond M e he) hX (fun _ => Or.inl rfl) (fun _ => Or.inr rfl)

end WaveTurbulence.GammaLow.FinalCount.H
