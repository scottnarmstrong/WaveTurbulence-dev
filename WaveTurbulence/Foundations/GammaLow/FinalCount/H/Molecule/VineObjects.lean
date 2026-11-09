/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineObjects`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Draft vine-like objects (TARGET defvine, defblock and vinechainlem)

These definitions supplement, without changing, the pinned B2 vine draft.
A chain records its ingredients in order. An HV is the adjoint of one vine;
an HVC has at least two ingredients. A DV shares exactly its two joints,
and therefore may share the bond between those joints.
-/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

-- (`IsSomeVine`: defined by L6 as `Src.IsSomeVine`)
-- (`Chain`: defined by L6 as `Src.Chain`)
-- (`IsVC`: defined by L6 as `Src.IsVC`)
-- (`IsHV`: defined by L6 as `Src.IsHV`)
-- (`IsHVC`: defined by L6 as `Src.IsHVC`)
-- (`IsDV`: defined by L6 as `Src.IsDV`)
-- (`IsVineLike`: defined by L6 as `Src.IsVineLike`)
/-- Every actual vine is a one-ingredient VC (low family: N2 Lemma 5.2). -/
theorem isVine_isVC {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (h : M.IsVine X S a b) : Src.IsVC Src.γL M S a b :=
  ⟨h.1,1,Src.Chain.single (Src.isSomeVine_of_isVine' h)⟩

/-- Every family member is a one-ingredient VC. -/
theorem isSomeVine_isVC {M : Molecule V D} {S : Finset V} {a b : V} (h : Src.IsSomeVine Src.γL M S a b) :
    Src.IsVC Src.γL M S a b :=
  ⟨h.block, 1, Src.Chain.single h⟩

omit [DecidableEq D] in
/-- Every chain has at least one ingredient. -/
theorem chain_pos {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain Src.γL M S a b n) : 1 ≤ n := by
  induction h with
  | single => exact le_rfl
  | append _ _ _ _ _ => omega

/-- Hyper-vines are actual hyper-blocks in the half-edge sense. -/
theorem isHV_isHyperBlock {M : Molecule V D} {S : Finset V} {a b : V}
    (h : Src.IsHV Src.γL M S a b) : Mole.IsHyperBlock M S a b := by
  obtain ⟨e,he,hX⟩ := h
  exact ⟨e,he,hX.block⟩

/-- Hyper-vine-chains are actual hyper-blocks. -/
theorem isHVC_isHyperBlock {M : Molecule V D} {S : Finset V} {a b : V}
    (h : Src.IsHVC Src.γL M S a b) : Mole.IsHyperBlock M S a b := by
  obtain ⟨e,he,hB,_⟩ := h
  exact ⟨e,he,hB⟩

end WaveTurbulence.GammaLow.FinalCount.H
