/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceV0` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceV0


/-!
# REDSPLICE-DEF (S2a), part 1: prescriptions and the collection `𝒱_0`

TARGET L1953-L1955 (section `redsplice`): the sum over a congruence class is divided into at most `3^n`
terms by specifying, for every vine-like object of the collection `𝒞` of `vinechainlem`, whether it is SG,
LG or ZG; `𝒱_0` is the collection of VCs in `𝒱` that are SG.

Reading (recorded): a *prescription* is a total function `σ` from atom sets to `GapKind`; only its values on
the groups of `𝒞 = maximalGroupsG γ G.molecule` matter.  The VCs of `𝒱` are recorded through their vine
ingredients (TARGET L1936: "the vines in `𝒱` can be arranged into finitely many disjoint VC's"); a vine of
`𝒱` lies in `𝒱_0` iff the group of `𝒞` containing it is SG (all ingredients of a chain share the gap of the
chain, TARGET L1938-L1941).  The splice itself (iterated CL splice, hinge atoms) is built on the canonical
CLCN port (UNIVERSE layer L2, ruling R8) and is not part of this module.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)]


/-- The vines of `𝒱_0`: vines of `𝒱` whose group in `𝒞` is prescribed SG.  B1a (ruling F-1): the trailing
marked vine set `Mk` (default `∅`) removes the marked vines, so `vinesV0 γ G σ Mk` is o75's `𝒱₀♮ = 𝒱₀ ∖ Mk`
(`RedSplice.vinesV0Mk_eq`); at `Mk = ∅` it is main's `𝒱_0` (`RedSplice.mem_vinesV0_empty`). -/
@[expose] def vinesV0 (γ : ℝ) (G : Garden w) (σ : Prescription G) (Mk : Set (CLVineG γ G) := ∅) : Set (CLVineG γ G) :=
  {c | c ∈ vinesVG γ G ∧ ∃ S ∈ maximalGroupsG γ G.molecule, IsIngredientG γ G.molecule S c.atoms ∧ σ S = .SG ∧ c ∉ Mk}

theorem vinesV0_subset (G : Garden w) (σ : Prescription G) : vinesV0 γ G σ ⊆ vinesVG γ G :=
  fun _ h => h.1

/-- B1a: `vinesV0` for every marked set lies in `𝒱`. -/
theorem vinesV0_subsetMk (G : Garden w) (σ : Prescription G) (Mk : Set (CLVineG γ G)) : vinesV0 γ G σ Mk ⊆ vinesVG γ G :=
  fun _ h => h.1

/-- B1a bridge: membership in `vinesV0` at the default `Mk = ∅` is main's membership. -/
theorem mem_vinesV0_empty {G : Garden w} {σ : Prescription G} {c : CLVineG γ G} :
    c ∈ vinesV0 γ G σ ↔ c ∈ vinesVG γ G ∧ ∃ S ∈ maximalGroupsG γ G.molecule, IsIngredientG γ G.molecule S c.atoms ∧ σ S = .SG :=
  ⟨fun ⟨hV, S, hS, hI, hσ, _⟩ => ⟨hV, S, hS, hI, hσ⟩, fun ⟨hV, S, hS, hI, hσ⟩ => ⟨hV, S, hS, hI, hσ, fun h => h⟩⟩

/-- B1a bridge: membership in `vinesV0` for a marked set. -/
theorem mem_vinesV0 {G : Garden w} {σ : Prescription G} {Mk : Set (CLVineG γ G)} {c : CLVineG γ G} :
    c ∈ vinesV0 γ G σ Mk ↔ c ∈ vinesV0 γ G σ ∧ c ∉ Mk :=
  ⟨fun ⟨hV, S, hS, hI, hσ, hc⟩ => ⟨⟨hV, S, hS, hI, hσ, fun h => h⟩, hc⟩,
    fun ⟨⟨hV, S, hS, hI, hσ, _⟩, hc⟩ => ⟨hV, S, hS, hI, hσ, hc⟩⟩

end WaveTurbulence.GammaLow.Fama
