/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Local
public import WaveTurbulence.Foundations.FinalCount.RedSpliceInduced
/-! # Isomorphism invariance of `𝒱_γ` along main's induced isomorphisms (packet L5a, item D)

Main's `RedSplice.InducedIso.isVine` transports the drawn vines along an isomorphism of induced subgraphs (used for the
splice map). `TVineIsoInvariant` is the same statement for T-vines. It is an obligation of L5a itself (not a named
input): it is carried as an instance while the piece construction is ported, and proved in `Vine/Iso.lean`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.GammaLow.FinalCount

/-- T-vines are invariant under isomorphisms of induced subgraphs (main's `InducedIso`). -/
def TVineIsoInvariant : Prop :=
  ∀ {V D V' D' : Type} [DecidableEq V] [Fintype D] [DecidableEq D] [DecidableEq V'] [Fintype D'] [DecidableEq D']
    {M : Molecule V D} {M' : Molecule V' D'} {B : Finset V} {B' : Finset V'} (I : RedSplice.InducedIso M M' B B')
    {a b : V}, M.IsTVine B a b → M'.IsTVine B' (I.π a) (I.π b)

/-- `𝒱_γ` is invariant under isomorphisms of induced subgraphs. -/
theorem isSomeVine_iso [h : Fact TVineIsoInvariant] {γ : ℝ} {V D V' D' : Type} [DecidableEq V] [Fintype D]
    [DecidableEq D] [DecidableEq V'] [Fintype D'] [DecidableEq D'] {M : Molecule V D} {M' : Molecule V' D'}
    {B : Finset V} {B' : Finset V'} (I : RedSplice.InducedIso M M' B B') {a b : V}
    (hv : Src.IsSomeVine γ M B a b) : Src.IsSomeVine γ M' B' (I.π a) (I.π b) := by
  rcases hv with ⟨hγ, hv | hv | hv⟩ | ⟨hγ, X, hv⟩
  · exact Or.inl ⟨hγ, Or.inl (I.isVine hv)⟩
  · exact Or.inl ⟨hγ, Or.inr (Or.inl (I.isVine hv))⟩
  · exact Or.inl ⟨hγ, Or.inr (Or.inr (h.out I hv))⟩
  · exact Or.inr ⟨hγ, X, I.isVine hv⟩

end WaveTurbulence.GammaLow.Fama
