/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineSGSingleVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.Member
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineSGSingleVine`** (sha256 in H/COPIED-SHA256SUMS), **restated over the
low family by L6-HDS** (PLAN-L6 §3e–3f, layer H-DS). Main's statement names the drawn vine types; in the low family
`𝒱_{γL}` a vine is of type (I), (II) or a T-vine, and the drawn-type classification is replaced by N3 Cor 1.16′
(`Src.DSInputs`, see `H/DS/Member.lean`). Low-range change: the outer vine is a member of the low family (`Src.IsSomeVine Src.γL`, main: `M.IsVine X` for a drawn
type `X`) and the third alternative is a T-vine (main: `X = .VII ∧ M.IsVine .V`). Main's `typeVII_inner_VC_isVineV` becomes
`inner_VC_isTVine` (a VC with more than three atoms avoiding the joints of a vine of the low family is a T-vine).

# SG VCs in a single vine of the low family -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- TARGET subsetvc, ordinary VC inside a single outer vine of the low family: the inner SG VC in an LG/ZG vine is one or
two double bonds, or a T-vine (N3 Cor 1.16′(2)). -/
theorem SG_VC_in_single_vine (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} (hV : Src.IsSomeVine Src.γL M S a b)
    {A : Finset V} {x y : V} (hVC : Src.IsVC Src.γL M A x y) (hAS : A ⊆ S)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0)
    {r r' : Mom d} (hr : M.IsBlockGap L w κ S a r) (hr' : M.IsBlockGap L w κ A x r')
    (houter : Molecule.gapKind L γ η r = .LG ∨ Molecule.gapKind L γ η r = .ZG)
    (hsmall : Molecule.gapKind L γ η r' = .SG) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 ∨ M.IsTVine A x y :=
  DS.SG_VC_in_vine hM hV hVC hAS L γ η w c κ hκ hc hr hr' houter hsmall

end WaveTurbulence.GammaLow.FinalCount.H
