/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL8
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CycN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL6
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.GL8`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **G3-LOWDEG (R48), part 8**: the auxiliary invariants (`DPInv`, `AncRel`, `DesRecN`, `EpsLe`) along the LOW run. -/
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
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}
variable {h h' : HSt V D₀}

/-- The auxiliary invariants. -/
def RunAux (M₀ : Molecule V D₀) (C : CollData M₀) (h : HSt V D₀) : Prop :=
  DPInv h ∧ AncRel M₀ h.s h.anc ∧ DesRecN C h

theorem RunAux.init (C : CollData M₀) : RunAux M₀ C (HSt.init M₀) := ⟨DPInv.init M₀, AncRel.init M₀, DesRecN.init C⟩

theorem DesRecN.vineD1 {C : CollData M₀} (hD : DesRecN C h) (hs : HStepD1 C L γ η w κ h h') : DesRecN C h' := by
  cases hs with
  | vine K' hu' hl' hd2' htwin' hsg' hnew hdu hdl =>
    have n1 : K'.fa ≠ K'.fb := K'.fa_ne_fb
    have n2 : K'.fa ≠ K'.C.lower := K'.fa_ne_b
    have n3 : K'.fb ≠ K'.C.upper := K'.fb_ne_a
    have n4 : K'.fa ≠ K'.C.upper := fun e => K'.fa_fresh (e ▸ K'.a_atom)
    have n5 : K'.fb ≠ K'.C.lower := fun e => K'.fb_fresh (e ▸ K'.b_atom)
    intro j p vis hj
    by_cases e1 : j = K'.fb
    · subst e1
      simp [FinalCountG3.HSt.vinePostGL, H.HSt.vinePostGL, Function.update_apply, n1.symm, n5, n3] at hj ⊢
      obtain ⟨rfl, -⟩ := hj
      simpa using hdl
    by_cases e2 : j = K'.C.lower
    · subst e2
      simp [FinalCountG3.HSt.vinePostGL, H.HSt.vinePostGL, Function.update_apply, e1, n2.symm, n5.symm] at hj ⊢
      obtain ⟨rfl, -⟩ := hj
      simpa [n2.symm, n5.symm] using hdl
    by_cases e3 : j = K'.fa
    · subst e3
      simp [FinalCountG3.HSt.vinePostGL, H.HSt.vinePostGL, Function.update_apply, e1, e2, n1, n2, n4] at hj ⊢
      obtain ⟨rfl, -⟩ := hj
      simpa using hdu
    by_cases e4 : j = K'.C.upper
    · subst e4
      simp [FinalCountG3.HSt.vinePostGL, H.HSt.vinePostGL, Function.update_apply, e1, e2, e3, n3.symm, n4.symm] at hj ⊢
      obtain ⟨rfl, -⟩ := hj
      simpa [n3.symm, n4.symm] using hdu
    · simp [FinalCountG3.HSt.vinePostGL, H.HSt.vinePostGL, Function.update_apply, e1, e2, e3, e4] at hj ⊢
      exact hD j p vis hj

theorem DesRecN.d3 {C : CollData M₀} (hD : DesRecN C h) (hs : HStepD3 C L γ η w κ h h') : DesRecN C h' := by
  cases hs with
  | cut v x₁ x₂ hv hε hd hx₁ hx₂ hne ho₁ ho₂ hnz hdes =>
    intro j p vis hj
    by_cases e : j = v
    · subst e
      simp [HSt.betaPost, Function.update_apply] at hj ⊢
      obtain ⟨rfl, -⟩ := hj
      exact hdes
    · simp [HSt.betaPost, Function.update_apply, e] at hj ⊢
      exact hD j p vis hj

theorem HStep1L.aux {C : CollData M₀} (hs : HStep1L C L γ η w κ h h') (ha : RunAux M₀ C h) : RunAux M₀ C h' := by
  obtain ⟨hdp, hA, hD⟩ := ha
  cases hs with
  | old hs =>
    refine ⟨?_, hs.anc hA, H.DesRecN.step1L hD hs⟩
    rcases hs.cases with h1 | h3
    · exact h1.dp hdp hA.inj
    · exact h3.toHStep3.dp hdp hA.inj
  | low hs =>
    obtain ⟨K, hu, hl, hd2, htwin, hsg, rfl⟩ := hs.data
    exact ⟨hdp.vinePostGL hA.inj K, hA.vinePostGL K, hD.vineD1 hs⟩

theorem HStepD3.aux {C : CollData M₀} (hs : HStepD3 C L γ η w κ h h') (ha : RunAux M₀ C h) : RunAux M₀ C h' := by
  obtain ⟨hdp, hA, hD⟩ := ha
  obtain ⟨v, x₁, x₂, hDa, rfl⟩ := hs.data
  exact ⟨hdp.betaPost hDa, hA.betaSt v, hD.d3 hs⟩

theorem HStep2C.aux {C : CollData M₀} (hs : HStep2C C L γ η w κ h h') (ha : RunAux M₀ C h) : RunAux M₀ C h' :=
  ⟨hs.toHStep2.dp ha.1 ha.2.1.inj, hs.toHStep2.anc ha.2.1, ha.2.2.step2 hs⟩

theorem HStep3C.aux {C : CollData M₀} (hs : HStep3C C L γ η w κ h h') (ha : RunAux M₀ C h) : RunAux M₀ C h' :=
  ⟨hs.toHStep3.dp ha.1 ha.2.1.inj, hs.toHStep3.anc ha.2.1, ha.2.2.step3 hs⟩

end WaveTurbulence.GammaLow.FinalCount.H
