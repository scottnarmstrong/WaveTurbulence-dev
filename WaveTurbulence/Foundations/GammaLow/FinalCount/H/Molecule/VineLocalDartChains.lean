/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainCounts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.VineLocalDartObjects
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineLocalDartChains`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Local dart identifications preserve actual chain decompositions -/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
variable {V D E : Type*} [DecidableEq V] [Fintype D] [Fintype E] [DecidableEq D] [DecidableEq E]
    {M : Molecule V D} {N : Molecule V E} {A : Finset V}
namespace LocalDartEmbedding
open WaveTurbulence.Vine.LocalDartEmbedding
variable (F : LocalDartEmbedding M N A)

include F in
/-- Every identified actual chain is also a chain in the original molecule. -/
theorem chain_toL {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain Src.γL N S a b n) :
    S ⊆ A → Src.Chain Src.γL M S a b n := by
  induction h with
  | single h =>
    intro hSA
    have hX := h
    exact Src.Chain.single ((F.isVine_iffS _ hSA _ _).mp hX)
  | @append S T a b c n hS hT hi hne ih =>
    intro hUA
    have hX := hT
    exact Src.Chain.append (ih (Finset.subset_union_left.trans hUA))
      ((F.isVine_iffS _ (Finset.subset_union_right.trans hUA) _ _).mp hX) hi hne

alias _root_.WaveTurbulence.Vine.LocalDartEmbedding.chain_toL := _root_.WaveTurbulence.GammaLow.FinalCount.H.LocalDartEmbedding.chain_toL
include F in
/-- Every original chain lifts through an identification of all its internal darts. -/
theorem chain_ofL {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain Src.γL M S a b n) :
    S ⊆ A → Src.Chain Src.γL N S a b n := by
  induction h with
  | single h =>
    intro hSA
    have hX := h
    exact Src.Chain.single ((F.isVine_iffS _ hSA _ _).mpr hX)
  | @append S T a b c n hS hT hi hne ih =>
    intro hUA
    have hX := hT
    exact Src.Chain.append (ih (Finset.subset_union_left.trans hUA))
      ((F.isVine_iffS _ (Finset.subset_union_right.trans hUA) _ _).mpr hX) hi hne

alias _root_.WaveTurbulence.Vine.LocalDartEmbedding.chain_ofL := _root_.WaveTurbulence.GammaLow.FinalCount.H.LocalDartEmbedding.chain_ofL
include F in
/-- Both source chain existence and the exact number of ingredients are preserved. -/
theorem chain_iffL (S : Finset V) (hSA : S ⊆ A) (a b : V) (n : ℕ) :
    Src.Chain Src.γL N S a b n ↔ Src.Chain Src.γL M S a b n :=
  ⟨fun h => F.chain_toL h hSA,fun h => F.chain_ofL h hSA⟩

alias _root_.WaveTurbulence.Vine.LocalDartEmbedding.chain_iffL := _root_.WaveTurbulence.GammaLow.FinalCount.H.LocalDartEmbedding.chain_iffL
include F in
/-- The source VC predicate, including the actual block premise, is preserved. -/
theorem isVC_iffL (S : Finset V) (hSA : S ⊆ A) (a b : V) : Src.IsVC Src.γL N S a b ↔ Src.IsVC Src.γL M S a b := by
  simp only [Src.IsVC,F.isBlock_iff S hSA a b,F.chain_iffL S hSA a b]

alias _root_.WaveTurbulence.Vine.LocalDartEmbedding.isVC_iffL := _root_.WaveTurbulence.GammaLow.FinalCount.H.LocalDartEmbedding.isVC_iffL
end LocalDartEmbedding
end WaveTurbulence.GammaLow.FinalCount.H
