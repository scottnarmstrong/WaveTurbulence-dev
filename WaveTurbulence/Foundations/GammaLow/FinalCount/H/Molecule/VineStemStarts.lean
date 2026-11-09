/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineStemStarts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineStemStarts`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # The stem-start double pairs in all eight pinned vine templates -/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc, first stem stage: source SG and outer LG/ZG gap
conditions force all listed stem-start pairs to be absent from an inner
VC larger than one double bond. Rung counts are completely arbitrary. -/
theorem SG_stemStarts_absent {d : ℕ} (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (hS : M.IsBlock S a b) {A : Finset V} {x y : V} (hVC : Src.IsVC Src.γL M A x y)
    (hAS : A ⊆ S) (hcard : 2<A.card) (L γ η : ℝ) (w : Mom d)
    (c : V → Mom d) (κ : D → (Fin d → ℤ)) (hκ : M.IsDecoration L w c κ)
    (hc : ∀ v ∈ M.atoms,M.deg v=4 → c v=0) {r r' : Mom d}
    (hr : M.IsBlockGap L w κ S a r) (hr' : M.IsBlockGap L w κ A x r')
    (houter : Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)
    (hsmall : Molecule.gapKind L γ η r'=.SG) :
    ∀ c ∈ stemStarts X,∀ v ∈ S,R.f v=c.upper ∨ R.f v=c.lower → v ∉ A := by
  have hj := SG_block_outer_joints_absent M hM hS hVC.1 hAS L γ η w c κ hκ hc hr hr' houter hsmall
  intro st hst
  exact stemStarts_absent M hM R hS hVC.1 (isVC_connected hVC) hcard hj.1 hj.2 st hst

end WaveTurbulence.GammaLow.FinalCount.H
