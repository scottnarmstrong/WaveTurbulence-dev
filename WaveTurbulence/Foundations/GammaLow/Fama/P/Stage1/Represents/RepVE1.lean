/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a-G port of main `WaveTurbulence.Foundations.Stage1.Represents.RepVE1` (sha256 in COPIED-SHA256SUMS-G) over 𝒱_γ:
-- the chain assembly is L5b's `Famb.VineEstS2.CLChainAssemblyΓ γ` (ingredients in `Src.IsSomeVine γ`).
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyPieces
public import WaveTurbulence.Foundations.Stage1.Represents.RepVE1
import Mathlib.Tactic
/-!
# S2 REPRESENTS, VINE-E over `𝒱_γ`: the pieces of a chain assembly are the members of its spine

`assemblyPieces_spine`: for a chain assembly `B` (L5b's `CLChainAssemblyΓ γ`) of a block `U` between `a` and `b`, the
atom sets of its pieces are exactly the atom sets of the members of a spine (`Spine γ`) of `U`. Main's family-free
parity lemmas `isBad_iff_even`, `isBad_unique` are used from main (`Represents.*`, imported).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.Represents
open Finset WaveTurbulence WaveTurbulence.GammaLow.FinalCount WaveTurbulence.RegRed

variable {w : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

theorem assemblyPieces_spine {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} (B : Famb.VineEstS2.CLChainAssemblyΓ γ G R n) :
    ∃ L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree), Spine γ G.molecule L U a b ∧
      L.length = n ∧ (∀ i : Fin n, ∃ p q, ((Famb.VineEstS2.assemblyPieceAtΓ B i).atoms, p, q) ∈ L) ∧
      (∀ T p q, (T, p, q) ∈ L → ∃ i : Fin n, (Famb.VineEstS2.assemblyPieceAtΓ B i).atoms = T) := by
  induction B with
  | @single U a b hV R =>
    refine ⟨_, Spine.one hV, rfl, fun i => ⟨a, b, by simp [Famb.VineEstS2.assemblyPieceAtΓ]⟩, ?_⟩
    intro T p q hm
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, -, -⟩ := hm
    exact ⟨0, rfl⟩
  | @append S T a b c n RP B hT hi hU R ih =>
    obtain ⟨L, hs, hl, h1, h2⟩ := ih
    refine ⟨L ++ [(T, b, c)], Spine.snoc hs hT hi hU.2.2.2.1, by simp [hl], ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨b, c, by simp [Famb.VineEstS2.assemblyPieceAtΓ]⟩
      · obtain ⟨p, q, hpq⟩ := h1 j
        exact ⟨p, q, List.mem_append_left _ (by simpa [Famb.VineEstS2.assemblyPieceAtΓ] using hpq)⟩
    · intro T' p q hm
      rcases List.mem_append.mp hm with h | h
      · obtain ⟨i, hi'⟩ := h2 T' p q h
        exact ⟨i.succ, by simpa [Famb.VineEstS2.assemblyPieceAtΓ] using hi'⟩
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, -, -⟩ := h
        exact ⟨0, by simp [Famb.VineEstS2.assemblyPieceAtΓ]⟩

end WaveTurbulence.GammaLow.Fama.Represents
