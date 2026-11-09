/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Anc
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RelRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3Anc`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: the ancestor map** `anc : V → V` of an `HSt` (E10): every atom of the current molecule has an
ancestor atom of `M_sub` (a cut half maps to the atom it was cut from, `ε`-atoms map to themselves), and the atom of a
dart of `M_sub` is the ancestor of the atom of the corresponding current dart. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

variable {M₀ : Molecule V D₀} {s : St.{u} V D₀} {a : V → V}

theorem HStep1.anc {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {h h' : HSt V D₀}
    (hs : HStep1 L γ η w κ h h') (hr : AncRel M₀ h.s h.anc) : AncRel M₀ h'.s h'.anc := by
  cases hs with
  | vine K R' kp hR hkp hu hl ga gb htwin hι₁ hι₂ hsg h3a h3b =>
    have hab := alphaOrBeta_isAB K.post.numComponents h.s.M.numComponents R' kp
    have hce := Cls.ne_eps_of_isAB hab
    have h1 := hr.cutSt K.C.upper K.fa K.x₁ K.x₂ _ _ hce hce K.cut_a
      (Function.update h.anc K.fa (h.anc K.C.upper)) (fun b => by
        by_cases e : b = K.fa
        · subst e; simp
        · simp [Function.update_of_ne e, e])
    have h2 := h1.cutSt K.C.lower K.fb K.y₁ K.y₂ _ _ hce hce K.cut_b
      (Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower)) (fun b => by
        by_cases e : b = K.fb
        · subst e; simp [Function.update_of_ne K.fa_ne_b.symm]
        · simp [Function.update_of_ne e, e])
    exact h2.delSt _ K.closed

theorem HRun.ancRel {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {hf : HSt V D₀}
    (hr : HRun L γ η w κ (HSt.init M₀) hf) : AncRel M₀ hf.s hf.anc := by
  obtain ⟨h₁, h₂, h₃, a1, _, a2, _, a3, _, a4, _⟩ := hr
  have r0 : AncRel M₀ (HSt.init M₀).s (HSt.init M₀).anc := AncRel.init M₀
  exact rtg_anc (fun _ _ h g => HStep4.anc h g) a4 (rtg_anc (fun _ _ h g => HStep3.anc h g) a3
    (rtg_anc (fun _ _ h g => HStep2.anc h g) a2 (rtg_anc (fun _ _ h g => HStep1.anc h g) a1 r0)))

end WaveTurbulence.GammaLow.FinalCount.H
