/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RedSpliceV0
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.S1Collection
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceV0`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# REDSPLICE-DEF (S2a), part 1: prescriptions and the collection `𝒱_0`

TARGET L1953-L1955 (section `redsplice`): the sum over a congruence class is divided into at most `3^n`
terms by specifying, for every vine-like object of the collection `𝒞` of `vinechainlem`, whether it is SG,
LG or ZG; `𝒱_0` is the collection of VCs in `𝒱` that are SG.

Reading (recorded): a *prescription* is a total function `σ` from atom sets to `GapKind`; only its values on
the groups of `𝒞 = maximalGroups G.molecule` matter.  The VCs of `𝒱` are recorded through their vine
ingredients (TARGET L1936: "the vines in `𝒱` can be arranged into finitely many disjoint VC's"); a vine of
`𝒱` lies in `𝒱_0` iff the group of `𝒞` containing it is SG (all ingredients of a chain share the gap of the
chain, TARGET L1938-L1941).  The splice itself (iterated CL splice, hinge atoms) is built on the canonical
CLCN port (UNIVERSE layer L2, ruling R8) and is not part of this module.
-/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.RedSplice
open WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ}

/-- The vines of `𝒱_0`: vines of `𝒱` whose group in `𝒞` is prescribed SG.  B1a (ruling F-1): the trailing
marked vine set `Mk` (default `∅`) removes the marked vines, so `vinesV0 G σ Mk` is o75's `𝒱₀♮ = 𝒱₀ ∖ Mk`
(`RedSplice.vinesV0Mk_eq`); at `Mk = ∅` it is main's `𝒱_0` (`mem_vinesV0_empty`). -/
@[expose] def vinesV0 (G : Garden w) (σ : Prescription G) (Mk : Set (CLVine G) := ∅) : Set (CLVine G) :=
  {c | c ∈ vinesV G ∧ ∃ S ∈ maximalGroups G.molecule, IsIngredient G.molecule S c.atoms ∧ σ S = .SG ∧ c ∉ Mk}

theorem vinesV0_subset (G : Garden w) (σ : Prescription G) : vinesV0 G σ ⊆ vinesV G :=
  fun _ h => h.1

/-- B1a: `vinesV0` for every marked set lies in `𝒱`. -/
theorem vinesV0_subsetMk (G : Garden w) (σ : Prescription G) (Mk : Set (CLVine G)) : vinesV0 G σ Mk ⊆ vinesV G :=
  fun _ h => h.1

/-- B1a bridge: membership in `vinesV0` at the default `Mk = ∅` is main's membership. -/
theorem mem_vinesV0_empty {G : Garden w} {σ : Prescription G} {c : CLVine G} :
    c ∈ vinesV0 G σ ↔ c ∈ vinesV G ∧ ∃ S ∈ maximalGroups G.molecule, IsIngredient G.molecule S c.atoms ∧ σ S = .SG :=
  ⟨fun ⟨hV, S, hS, hI, hσ, _⟩ => ⟨hV, S, hS, hI, hσ⟩, fun ⟨hV, S, hS, hI, hσ⟩ => ⟨hV, S, hS, hI, hσ, fun h => h⟩⟩

/-- B1a bridge: membership in `vinesV0` for a marked set. -/
theorem mem_vinesV0 {G : Garden w} {σ : Prescription G} {Mk : Set (CLVine G)} {c : CLVine G} :
    c ∈ vinesV0 G σ Mk ↔ c ∈ vinesV0 G σ ∧ c ∉ Mk :=
  ⟨fun ⟨hV, S, hS, hI, hσ, hc⟩ => ⟨⟨hV, S, hS, hI, hσ, fun h => h⟩, hc⟩,
    fun ⟨⟨hV, S, hS, hI, hσ, _⟩, hc⟩ => ⟨hV, S, hS, hI, hσ, hc⟩⟩

end WaveTurbulence.GammaLow.FinalCount.H
