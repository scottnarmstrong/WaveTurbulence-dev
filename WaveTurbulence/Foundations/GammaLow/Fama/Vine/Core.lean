/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.Molecule.CoreVine
/-! # Core (drawn) vines are members of `𝒱_γ` (packet L5a, item F)

Main's core CL vines (`IsCoreCLVine G X S a b`: a drawn vine of type (I) or (II) with the CL parent pattern) are
drawn vines of type (I) or (II), hence members of `𝒱_γ` for every `γ ≤ 1/2` (D11, first two disjuncts of
`IsVineEnl`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.GammaLow.FinalCount WaveTurbulence.Twist

variable {w : ℕ} {G : Garden w}

/-- A drawn vine of type (I) or (II) is a member of `𝒱_γ` (`γ ≤ 1/2`). -/
theorem isSomeVine_of_core {γ : ℝ} [hγ : Fact (γ ≤ 1 / 2)] {X : VineType} {S : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (h : IsCoreCLVine G X S a b) : Src.IsSomeVine γ G.molecule S a b := by
  rcases h.2.2 with rfl | ⟨rfl, -⟩
  · exact Or.inl ⟨hγ.out, Or.inl h.1⟩
  · exact Or.inl ⟨hγ.out, Or.inr (Or.inl h.1)⟩

end WaveTurbulence.GammaLow.Fama
