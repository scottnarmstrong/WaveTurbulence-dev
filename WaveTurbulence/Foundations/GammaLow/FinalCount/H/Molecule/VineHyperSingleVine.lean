/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineHyperSingleVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineCapAdjointClassification
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineHyperSingleVine`** (sha256 in H/COPIED-SHA256SUMS), **restated over the
low family by L6-HDS** (PLAN-L6 §3e–3f, layer H-DS). Main's statement names the drawn vine types; in the low family
`𝒱_{γL}` a vine is of type (I), (II) or a T-vine, and the drawn-type classification is replaced by N3 Cor 1.16′
(`Src.DSInputs`, see `H/DS/Member.lean`). Low-range change: the outer vine is a member of the low family (`Src.IsSomeVine Src.γL`, main: `M.IsVine X`) and the
adjoint alternative is a T-vine (main: a vine (V)).

# Hyper objects in a single vine of the low family -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- TARGET Lemma subsetvc, hyper-object clause inside a single vine of the low family: every contained HV/HVC has a
designated adjoint consisting of two double bonds or a T-vine. No gap assumption is required. -/
theorem hyperLike_in_single_vine_adjoint (M : Molecule V D)
    {S A : Finset V} {a b x y : V} (hV : Src.IsSomeVine Src.γL M S a b)
    (hAS : A ⊆ S) (h : Src.IsHV Src.γL M A x y ∨ Src.IsHVC Src.γL M A x y) :
    ∃ e : D, M.ends e = s(x, y) ∧
      (DoubleChain (Mole.eraseBond M e) A x y 2 ∨ (Mole.eraseBond M e).IsTVine A x y) := by
  obtain ⟨R⟩ := DS.hyperLike_realization h
  exact hyper_realization_in_vine M hV R hAS

end WaveTurbulence.GammaLow.FinalCount.H
