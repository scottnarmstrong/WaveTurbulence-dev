/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineLikeConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineLikeConnected`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Connectivity of all drafted vine-like objects (TARGET defvine) -/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET defvine: every hyper-vine is connected. -/
theorem isHV_connected {M : Molecule V D} {S : Finset V} {a b : V}
    (h : Src.IsHV Src.γL M S a b) : GroupConnected M S := by
  obtain ⟨e,_he,hX⟩ := h
  intro u hu v hv
  exact eraseBond_induced_path M e S ((Src.IsSomeVine.vconnected hX) u hu v hv)

/-- TARGET defvine: every hyper-vine-chain is connected. -/
theorem isHVC_connected {M : Molecule V D} {S : Finset V} {a b : V}
    (h : Src.IsHVC Src.γL M S a b) : GroupConnected M S := by
  obtain ⟨e,_he,_hB,n,_hn,hchain⟩ := h
  intro u hu v hv
  exact eraseBond_induced_path M e S (chain_connected hchain u hu v hv)

/-- TARGET vinechainlem: a DV is connected through either common joint. -/
theorem isDV_connected {M : Molecule V D} {S : Finset V} {a b : V}
    (h : Src.IsDV Src.γL M S a b) : GroupConnected M S := by
  obtain ⟨-, A,B,hA,hB,_hi,rfl⟩ := h
  exact groupConnected_union M ((Src.IsSomeVine.vconnected hA)) ((Src.IsSomeVine.vconnected hB)) (Src.isBlock_of_isSomeVine hA).2.1 (Src.isBlock_of_isSomeVine hB).2.1

/-- All three classes called vine-like in defvine are connected. -/
theorem isVineLike_connected {M : Molecule V D} {S : Finset V} {a b : V}
    (h : Src.IsVineLike Src.γL M S a b) : GroupConnected M S := by
  rcases h with h | h | h
  · exact isVC_connected h
  · exact isHV_connected h
  · exact isHVC_connected h

end WaveTurbulence.GammaLow.FinalCount.H
