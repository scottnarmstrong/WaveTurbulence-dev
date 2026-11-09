/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineCapAdjointClassification
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.Member
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineCapAdjointClassification`** (sha256 in H/COPIED-SHA256SUMS), **restated over the
low family by L6-HDS** (PLAN-L6 §3e–3f, layer H-DS). Main's statement names the drawn vine types; in the low family
`𝒱_{γL}` a vine is of type (I), (II) or a T-vine, and the drawn-type classification is replaced by N3 Cor 1.16′
(`Src.DSInputs`, see `H/DS/Member.lean`). Low-range change: main's cap classification `CapPrefixData.hyperLike_adjoint_classificationL`
(the adjoint is two double bonds or a vine (V), by the cap incidences of the drawn templates) becomes
`hyper_realization_in_vine`: a hyper object nested in a vine of the low family has, for its designated bond, an adjoint
that is two double bonds or a T-vine (N3 Cor 1.16′(2); no cap data).

# The adjoint classification of hyper objects in a vine of the low family -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- TARGET subsetvc's hyper clause for a realization: a hyper object nested in a vine of the low family has a designated
adjoint that is two double bonds or a T-vine. No gap premise. -/
theorem hyper_realization_in_vine (M : Molecule V D) {S A : Finset V} {a b x y : V}
    (hV : Src.IsSomeVine Src.γL M S a b) (R : Src.HyperLikeRealization Src.γL M A x y) (hAS : A ⊆ S) :
    ∃ e : D, M.ends e = s(x, y) ∧
      (DoubleChain (Mole.eraseBond M e) A x y 2 ∨ (Mole.eraseBond M e).IsTVine A x y) :=
  DS.hyper_in_vine hV R hAS

end WaveTurbulence.GammaLow.FinalCount.H
