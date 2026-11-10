/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceChainSwap`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Reversal of vine chains and the union of two ordinary objects at one joint. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine.SourceVine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem isSomeVine_swap {S : Finset V} {a b : V} (h : Src.IsSomeVine Src.γL M S a b) :
    Src.IsSomeVine Src.γL M S b a := by
  have hX := h
  exact (Src.IsSomeVine.swap hX)

theorem chain_swap {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain Src.γL M S a b n) :
    Src.Chain Src.γL M S b a n := by
  induction h with
  | single h => exact Src.Chain.single (isSomeVine_swap h)
  | @append S T a b c n hS hT hi hne ih =>
    have h1 : Src.Chain Src.γL M T c b 1 := Src.Chain.single (isSomeVine_swap hT)
    have h2 := chain_append_chain h1 ih (by rw [Finset.inter_comm]; exact hi)
    rw [Finset.union_comm] at h2
    rwa [Nat.add_comm] at h2

/-- Two ordinary chain objects meeting exactly at the joint `c`. -/
theorem chain_union_of_one_joint {S T : Finset V} {a b c : V} {n m : ℕ}
    (hS : Src.Chain Src.γL M S a c n) (hT : Src.Chain Src.γL M T c b m) (hST : S ∩ T = {c}) :
    Src.Chain Src.γL M (S ∪ T) a b (n + m) := chain_append_chain hS hT hST

end WaveTurbulence.GammaLow.FinalCount.H
