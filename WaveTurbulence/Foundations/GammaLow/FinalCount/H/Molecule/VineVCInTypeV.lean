/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineVCInTypeV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.Member
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineVCInTypeV`** (sha256 in H/COPIED-SHA256SUMS), **restated over the
low family by L6-HDS** (PLAN-L6 §3e–3f, layer H-DS). Main's statement names the drawn vine types; in the low family
`𝒱_{γL}` a vine is of type (I), (II) or a T-vine, and the drawn-type classification is replaced by N3 Cor 1.16′
(`Src.DSInputs`, see `H/DS/Member.lean`). Low-range change: main's `VC_in_typeV` (a VC nested in a vine (V)) becomes `VC_in_TVine` (a VC nested in a T-vine; the branches of a DV′
of the low family are T-vines).

# Every VC contained in a T-vine is one or two double bonds or a T-vine -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- TARGET subsetvc's structural case for a DV′ branch, without any decoration or gap hypothesis: every VC nested in a
T-vine is one/two double bonds or a T-vine (the whole T-vine, or a member of it, N3 Cor 1.16′(2)). -/
theorem VC_in_TVine (M : Molecule V D) {A S : Finset V} {a b x y : V} (hV : M.IsTVine S a b)
    (hA : Src.IsVC Src.γL M A x y) (hAS : A ⊆ S) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 ∨ M.IsTVine A x y :=
  DS.vc_in_tvine hV hA hAS

end WaveTurbulence.GammaLow.FinalCount.H
