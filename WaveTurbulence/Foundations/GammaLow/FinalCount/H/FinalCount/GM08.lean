/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GM08
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Dart
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3FinalCopy
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RunE
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RunN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.GM08`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: assembly of `FinalDec` for a component** of the final molecule, from the proved fields and the
single field `vineLG`, which is taken as the named conditional input `VineLGAtL` (see HANDOFF: it requires the
subpro (f) obligation and the identification of a final vine component with an object of `M_sub`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {R : ℕ} {Tm : V → Prop} {hf : HSt V D₀}

/-- The `vineLG` field of G8's `FinalDec` for the component of `a₀`, as a statement about the admissible
decorations (CONDITIONAL helper: this is the conclusion of DH23 Prop 9.5, last sentence, L1806; it is not proved
here). -/
def VineLGAtL (L γ η : ℝ) (hf : HSt V D₀) (a₀ : V) (AdmRun : (D₀ → (Fin d → ℤ)) → Prop) : Prop :=
  ((∃ j₁ j₂, (compMol hf.s.M a₀).IsVineEnl (compMol hf.s.M a₀).atoms j₁ j₂) ∨
    ((compMol hf.s.M a₀).atoms.card = 2 ∧ ∀ a ∈ (compMol hf.s.M a₀).atoms, (compMol hf.s.M a₀).deg a = 2)) →
  ∀ κ', compAdmL hf a₀ AdmRun κ' → ∀ x y, (compMol hf.s.M a₀).atom x = (compMol hf.s.M a₀).atom y →
    (compMol hf.s.M a₀).out x ≠ (compMol hf.s.M a₀).out y →
    L ^ (-γ + η) < ‖Molecule.kvec L (0 : Mom d) κ' x - Molecule.kvec L (0 : Mom d) κ' y‖

theorem finalDec_comp_of_vineL [Infinite V] (AdmRun : (D₀ → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, AdmRun κ → Prop95ConclAtL L γ η (0 : Mom d) κ R hf Tm) (hne : ∃ κ, AdmRun κ) (hL : 1 ≤ L)
    (hη : 0 ≤ η) {a₀ : V} (ha₀ : a₀ ∈ hf.s.M.atoms) (hT : TameFree hf Tm a₀) (hvine : VineLGAtL L γ η hf a₀ AdmRun) :
    FinalDec (compMol hf.s.M a₀) (fun a => toCls (hf.s.cls a)) L γ η (compAdmL hf a₀ AdmRun) where
  labRange := by
    intro a ha hα
    obtain ⟨κ₀, h₀⟩ := hne
    exact dec_labRangeL (hAdm κ₀ h₀) ((mem_compMol _ _).1 ha).1 hα
  kapVals := by
    intro a ha hα
    obtain ⟨κ₀, h₀⟩ := hne
    exact dec_kapValsL (hAdm κ₀ h₀) ((mem_compMol _ _).1 ha).1 hα
  epsLG := by
    rintro κ' ⟨κ, hκ, rfl⟩ a ha hε x y hx hy hxy
    exact dec_epsLGL (hAdm κ hκ) ((mem_compMol _ _).1 ha).1 (toCls_isEps.1 hε)
      (hT.of_sc ((mem_compMol _ _).1 ha).2) x y hx hy hxy
  alphaGap := by
    rintro κ' ⟨κ, hκ, rfl⟩ a ha hα x y hx hy hxy
    exact dec_alphaGapL (hAdm κ hκ) ((mem_compMol _ _).1 ha).1 hα hx hy (fun e => hxy (Subtype.ext e))
  alphaSG := by
    rintro κ' ⟨κ, hκ, rfl⟩ a ha hα x y hx hy hxy
    exact dec_alphaSGL (hAdm κ hκ) ((mem_compMol _ _).1 ha).1 hα hx hy (fun e => hxy (Subtype.ext e))
  betaGap := by
    rintro κ' ⟨κ, hκ, rfl⟩ a ha hβ x y hx hy hxy
    exact dec_betaGapL (hAdm κ hκ) ((mem_compMol _ _).1 ha).1 hβ hx hy (fun e => hxy (Subtype.ext e))
  vineLG := hvine
  noBetaCut := by
    rintro κ' ⟨κ, hκ, rfl⟩ v hv h3 v₂ x₁ x₂ hcd hg
    exact dec_noBetaCutL (hAdm κ hκ) hv h3 hcd hg
  iota := by
    rintro κ' ⟨κ, hκ, rfl⟩ v₁ h1 v₂ h2 v₃ h3 - hα1 hα2 hβ hk x₁ y₁ x₂ y₂ x₃ y₃ hx₁ hy₁ hn₁ hx₂ hy₂ hn₂ hx₃ hy₃ hn₃
      - - - hsum
    exact dec_iotaL (hAdm κ hκ) hL hη ((mem_compMol _ _).1 h1).1 ((mem_compMol _ _).1 h2).1
      ((mem_compMol _ _).1 h3).1 hα1 hα2 hβ hk hx₁ hy₁ (fun e => hn₁ (Subtype.ext e)) hx₂ hy₂
      (fun e => hn₂ (Subtype.ext e)) hx₃ hy₃ (fun e => hn₃ (Subtype.ext e)) hsum

end WaveTurbulence.GammaLow.FinalCount.H
