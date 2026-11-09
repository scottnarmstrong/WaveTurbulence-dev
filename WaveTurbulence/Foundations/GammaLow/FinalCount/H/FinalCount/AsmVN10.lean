/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmVN10
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN9
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproDisjFinal
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmVN10`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (VineNodeExists, part 10): `hsgC` and `hdesC` for the collected objects.**  `hingeData_collection` (a `C₁` object:
from `SubproOblG`'s `hingeSG`/`hingeJoint`), `hingeData_c2Of` (a `C₂` object lies in a host disjoint from the hinges, so its joints are
no hinges: vacuous), `hsg_c2Of` (pool objects are `SG`), `hsg_collection` (from the named class fact `C₁` is `SG`). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {V : Type*} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- A collection object satisfies `HingeData` (TARGET `subpro` (5)). -/
theorem hingeData_collection {M₀ : Molecule V D₀} {C : CollData M₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}
    (obl : SubproOblG C L γ η w κ) (i : Fin C.n) : HingeData C (C.collection i) := by
  intro v hv hvi
  obtain ⟨f, s, hf, hs, hP⟩ := obl.hingeJoint v hv i hvi
  obtain ⟨f', s', hf', hs', hT⟩ := obl.hingeSG v hv
  have e1 : f' = f := Option.some.inj (hf'.symm.trans hf)
  have e2 : s' = s := Option.some.inj (hs'.symm.trans hs)
  subst e1 e2
  exact ⟨f', s', hf, hs, hP.1, hP.2, hT.1.1, hT.1.2.1, hT.1.2.2.2⟩

/-- A `C₂` object has no hinge joint (`S4-DISJ`: it lies in a host disjoint from the hinges). -/
theorem hingeData_c2Of {M₀ : Molecule V D₀} {C : CollData M₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}
    {Unsel : Set (Src.Object Src.γL M₀)} {U : Src.Object Src.γL M₀} (hU : U ∈ C.C2Of L γ η w κ Unsel) : HingeData C U := by
  intro v hv hvU
  exfalso
  have hdis := (c2Of_disjoint_c1_hinges C hU).2
  have hmem : v ∈ U.atoms := object_mem_of_joint U hvU
  exact Finset.disjoint_left.mp hdis hmem hv

/-- A pool object is `SG`. -/
theorem hsg_c2Of {M₀ : Molecule V D₀} {C : CollData M₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}
    {Unsel : Set (Src.Object Src.γL M₀)} {U : Src.Object Src.γL M₀} (hU : U ∈ C.C2Of L γ η w κ Unsel) : U.HasGapKind L γ η w κ .SG :=
  hU.1.1.1

theorem collected_sg_hinge {M₀ : Molecule V D₀} {C : CollData M₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}
    {Un : Set (Src.Object Src.γL M₀)} (obl : SubproOblG C L γ η w κ) (hC1 : ∀ i, (C.collection i).HasGapKind L γ η w κ .SG)
    {U : Src.Object Src.γL M₀} (hU : Collected C Un L γ η w κ U) : U.HasGapKind L γ η w κ .SG ∧ HingeData C U := by
  rcases hU with ⟨i, rfl⟩ | hU
  · exact ⟨hC1 i, hingeData_collection obl i⟩
  · exact ⟨hsg_c2Of hU.1, hingeData_c2Of hU.1⟩

end WaveTurbulence.GammaLow.FinalCount.H
