/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3VineObj2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.G3GroupIso
/-! # H-TV (2): T-vines in main's `G3VineObj2` (packet L6-HTV)

T-analogues (`…T`) and low-family forms (`…S`, `Src.IsSomeVine Src.γL`) of main's `FinalCountG3.final_vine_vc` and
`FinalCountG3.final_vine_hv` (`FinalCount/G3VineObj2.lean`, sha256 in `COPIED-SHA256SUMS`), with the same hypotheses.
The `…T` proofs are main's, with `GroupIso.isVine` replaced by `GroupIso.isVineT`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H.TV
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {M₀ : Molecule V D₀} {hf : HSt V D₀} {a₀ j₁ j₂ : V}

/-- T-analogue of `final_vine_vc`: no extra bond, the component is a T-vine of `M_sub` on the ancestor group. -/
theorem final_vine_vcT {R : ℕ} (J : FinalJoints hf a₀ j₁ j₂) (hA : AncRel M₀ hf.s hf.anc)
    (hD : DartRel M₀ hf.s) (hS : SubHyp R M₀)
    (hv : (compMol hf.s.M a₀).IsTVine (compMol hf.s.M a₀).atoms j₁ j₂)
    (hne : ∀ z, ¬ IsExtra hf a₀ M₀ z) : M₀.IsTVine (AncGroup hf a₀) (hf.anc j₁) (hf.anc j₂) := by
  have G := comp_groupIso hA hD a₀ (J.injOn hA hD hS) (fun z hz => by
    by_contra hc
    exact hne z ⟨hz, hc⟩)
  exact G.isVineT (ancGroup_sub hA) hv

/-- Low-family form of `final_vine_vc`. -/
theorem final_vine_vcS {R : ℕ} (J : FinalJoints hf a₀ j₁ j₂) (hA : AncRel M₀ hf.s hf.anc)
    (hD : DartRel M₀ hf.s) (hS : SubHyp R M₀)
    (hv : Src.IsSomeVine Src.γL (compMol hf.s.M a₀) (compMol hf.s.M a₀).atoms j₁ j₂)
    (hne : ∀ z, ¬ IsExtra hf a₀ M₀ z) : Src.IsSomeVine Src.γL M₀ (AncGroup hf a₀) (hf.anc j₁) (hf.anc j₂) := by
  rcases hv.cases with h | h | h
  · exact Src.isSomeVine_of_I (final_vine_vc J hA hD hS h hne)
  · exact Src.isSomeVine_of_II (final_vine_vc J hA hD hS h hne)
  · exact Src.isSomeVine_of_T (final_vine_vcT J hA hD hS h hne)

/-- T-analogue of `final_vine_hv`: one extra bond `e`, the component is a T-vine of `M_sub` with `e` erased. -/
theorem final_vine_hvT {R : ℕ} (J : FinalJoints hf a₀ j₁ j₂) (hA : AncRel M₀ hf.s hf.anc)
    (hD : DartRel M₀ hf.s) (hS : SubHyp R M₀)
    (hv : (compMol hf.s.M a₀).IsTVine (compMol hf.s.M a₀).atoms j₁ j₂)
    {e : D₀} (he : IsExtra hf a₀ M₀ e) (hall : ∀ z, IsExtra hf a₀ M₀ z → z = e ∨ z = M₀.mate e) :
    M₀.ends e = s(hf.anc j₁, hf.anc j₂) ∧
      (Molecule.eraseBond M₀ e).IsTVine (AncGroup hf a₀) (hf.anc j₁) (hf.anc j₂) := by
  obtain ⟨ι, -, G⟩ := hv_groupIso J hA hD hS he hall
  refine ⟨?_, G.isVineT (ancGroup_sub hA) hv⟩
  rcases he.ends J hA hD hS with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [Molecule.ends, h1, h2]
  · simp [Molecule.ends, h1, h2, Sym2.eq_swap]

/-- Low-family form of `final_vine_hv`. -/
theorem final_vine_hvS {R : ℕ} (J : FinalJoints hf a₀ j₁ j₂) (hA : AncRel M₀ hf.s hf.anc)
    (hD : DartRel M₀ hf.s) (hS : SubHyp R M₀)
    (hv : Src.IsSomeVine Src.γL (compMol hf.s.M a₀) (compMol hf.s.M a₀).atoms j₁ j₂)
    {e : D₀} (he : IsExtra hf a₀ M₀ e) (hall : ∀ z, IsExtra hf a₀ M₀ z → z = e ∨ z = M₀.mate e) :
    M₀.ends e = s(hf.anc j₁, hf.anc j₂) ∧
      Src.IsSomeVine Src.γL (Molecule.eraseBond M₀ e) (AncGroup hf a₀) (hf.anc j₁) (hf.anc j₂) := by
  rcases hv.cases with h | h | h
  · exact (final_vine_hv J hA hD hS h he hall).imp_right Src.isSomeVine_of_I
  · exact (final_vine_hv J hA hD hS h he hall).imp_right Src.isSomeVine_of_II
  · exact (final_vine_hvT J hA hD hS h he hall).imp_right Src.isSomeVine_of_T

end WaveTurbulence.GammaLow.FinalCount.H.TV
