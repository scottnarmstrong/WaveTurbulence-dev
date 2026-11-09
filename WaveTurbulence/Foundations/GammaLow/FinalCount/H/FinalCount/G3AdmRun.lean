/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3AdmRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Anc
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Hist
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3UStep
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Statement
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDev
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3AdmRun`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: `AtomRelU` along the steps** (excessprop1 (1), `ι`-glue).

`EpsPin`: the charge of an `ε`-atom is constant on the class `Adm0` (derived from `M_sub` by `AncRel`/`DartRel`).
`AtomRelU` is preserved by the uniform Steps 1, 3 and 4 (Step 2 in `G3AdmRun2`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {L : ℝ} {w : Mom d}

/-! ### Step 3 and Step 4 -/

/-! ### Step 1 -/

theorem AtomRelU.step1L {h : HSt V D₀} (hR : AtomRelU Adm0 L w h) (hpin : EpsPin Adm0 L w h) (K : Step1.VineCut Src.γL h.s.M)
    (hu : h.s.cls K.C.upper = .eps) (hl : h.s.cls K.C.lower = .eps) (R : ℝ) (kp : ℕ) :
    AtomRelU Adm0 L w (h.vinePostL K R kp) := by
  set hc : Cls := alphaOrBeta K.post.numComponents h.s.M.numComponents R kp with hhc
  have hup : K.C.upper ∈ h.s.M.atoms := Step1.objectAtoms_sub K.C K.a_mem
  have hlo : K.C.lower ∈ h.s.M.atoms := Step1.objectAtoms_sub K.C K.b_mem
  have h1 := (hR.toX (ex := fun _ => False)).cut_pin K.cut_a hc hc (h.s.pr K.x₁ K.x₂ :: h.hist)
    (Function.update h.anc K.fa (h.anc K.C.upper)) h.alive (hpin _ hup hu)
  -- second cut, in the state after the first cut
  obtain ⟨cl, hcl⟩ := hpin _ hlo hl
  have hpin2 : ∃ c : Mom d, ∀ k0, Adm0 k0 →
      chargeAt (h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ hc hc).M L w (k0 ∘ (h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ hc hc).down)
        K.C.lower = c := by
    refine ⟨cl, fun k0 hk0 => ?_⟩
    show chargeAt (h.s.M.cut K.C.upper K.fa K.x₁ K.x₂) L w (k0 ∘ h.s.down) K.C.lower = cl
    rw [chargeAt_cut_other h.s.M K.cut_a K.ab_ne.symm K.fa_ne_b.symm]
    exact hcl k0 hk0
  have h2 := h1.cut_pin (h := ⟨h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ hc hc, h.s.pr K.x₁ K.x₂ :: h.hist,
      Function.update (Function.update h.crec K.C.upper (some (h.s.pr K.x₁ K.x₂, h.alive))) K.fa
        (some (h.s.pr K.x₁ K.x₂, h.alive)), Function.update h.anc K.fa (h.anc K.C.upper)⟩) K.cut_b hc hc
    (h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist) (Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower))
    (h.s.pr K.x₁ K.x₂ :: h.alive) hpin2
  exact (AtomRelX.del h2 (fun a => a ∉ K.C.atoms) K.closed (fun a _ _ hx => hx.1.1) _ _).toU


alias _root_.WaveTurbulence.FinalCountG3.AtomRelU.step1L := _root_.WaveTurbulence.GammaLow.FinalCount.H.AtomRelU.step1L
/-! ### Step 2 -/

end WaveTurbulence.GammaLow.FinalCount.H
