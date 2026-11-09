/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3NoTriple`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: no triple bond in `𝕄_fin`** (DH23 L1806, L1816: "any triple bond is destroyed in Step 1").

`EpsLe s₁ s`: the `ε`-atoms of `s` are `ε`-atoms of `s₁` and the number of bonds between two of them did not
increase.  It holds along Steps 2-4; an atom of class `≠ ε` has degree `≤ 2`, so no triple bond involves it. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ}

theorem Step1.epsLe {s s' : St.{u} V D₀} (h : Step1 L γ η w κ s s') : EpsLe s s' := by
  cases h with
  | vine K R kp hR hkp hu hl ga gb h3a h3b =>
    have hab := Cls.ne_eps_of_isAB (alphaOrBeta_isAB K.post.numComponents s.M.numComponents R kp)
    have e1 := EpsLe.cutSt s K.x₁ K.x₂ K.cut_a.1 K.cut_a.2.1 _ _ hab hab
    have e2 := EpsLe.cutSt (s.cutSt K.C.upper K.fa K.x₁ K.x₂ (alphaOrBeta K.post.numComponents s.M.numComponents R kp)
      (alphaOrBeta K.post.numComponents s.M.numComponents R kp)) K.y₁ K.y₂ K.cut_b.1 K.cut_b.2.1 _ _ hab hab
    exact (e1.trans e2).trans (EpsLe.delSt _ _ K.closed)

/-- **No triple bond in `𝕄_fin`** (L1806, L1816). -/
theorem Run.noTriple {sf s₀ : St.{u} V D₀} (hr : Run L γ η w κ s₀ sf) (hg : Good R sf) :
    NoTripleBond sf.M := by
  obtain ⟨s₁, s₂, s₃, h1, n1, h2, -, h3, -, h4, -⟩ := hr
  have e := ((epsLe_rtg (fun _ _ h => h.epsLe) h2).trans (epsLe_rtg (fun _ _ h => h.epsLe) h3)).trans
    (epsLe_rtg (fun _ _ h => h.epsLe) h4)
  intro a ha b hb hab
  by_contra hcon
  push Not at hcon
  have hda : 3 ≤ sf.M.deg a := (hcon.trans' (le_refl _)).trans (bondsBetween_le_deg _ _ _)
  have hdb : 3 ≤ sf.M.deg b := by
    have : sf.M.bondsBetween a b = sf.M.bondsBetween b a := by
      unfold Molecule.bondsBetween
      simp only [Sym2.eq_swap]
    rw [this] at hcon
    exact hcon.trans (bondsBetween_le_deg _ _ _)
  have hea : sf.cls a = .eps := by
    by_contra hne; have := (hg.1.ab a ha hne).1; omega
  have heb : sf.cls b = .eps := by
    by_contra hne; have := (hg.1.ab b hb hne).1; omega
  obtain ⟨⟨a1, -⟩, ⟨b1, -⟩, hle⟩ := e a ha b hb hea heb
  exact absurd (hcon.trans hle) (by have := n1 a a1 b b1 hab; omega)

end WaveTurbulence.GammaLow.FinalCount.H
