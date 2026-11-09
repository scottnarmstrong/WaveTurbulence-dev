/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3UStep
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Hist
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
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
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3UStep`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: the steps for a whole admissible class** (excessprop1 (1): "each step condition must hold for every
admissible decoration").

`UStepk … Adm0 h h'` is `HStepk` with every κ-dependent condition required for all `k0 ∈ Adm0`; the data of the step
(atoms, darts, label `R`, parameter `kp`) are the same for all decorations of the class.  The `ι` conditions are in the
uniform form: `kp = 50` requires an earlier cut, still carried by a present atom, that hits for all `k0 ∈ Adm0` with one
sign (`IotaUnif`, the fixed ball of DH23 L1801 / TARGET Remark `remiota`); `kp = 0` requires that no earlier cut hits.
`UStepk.hstep` : for every `κ ∈ Adm0` the step is an `HStepk`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-! ### The post states (copied from the targets of `HStep1..4`) -/

noncomputable def HSt.vinePostL (h : HSt V D₀) (K : Step1.VineCut Src.γL h.s.M) (R : ℝ) (kp : ℕ) : HSt V D₀ :=
  ⟨vineSt h.s K (alphaOrBeta K.post.numComponents h.s.M.numComponents R kp),
   h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist,
   Function.update (Function.update (Function.update (Function.update h.crec K.C.upper
     (some (h.s.pr K.x₁ K.x₂, h.alive))) K.fa (some (h.s.pr K.x₁ K.x₂, h.alive))) K.C.lower
     (some (h.s.pr K.y₁ K.y₂, h.s.pr K.x₁ K.x₂ :: h.alive))) K.fb
     (some (h.s.pr K.y₁ K.y₂, h.s.pr K.x₁ K.x₂ :: h.alive)),
   Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower)⟩

alias _root_.WaveTurbulence.FinalCountG3.HSt.vinePostL := _root_.WaveTurbulence.GammaLow.FinalCount.H.HSt.vinePostL
/-! ### The uniform steps -/

inductive UStep1 (L γ η : ℝ) (w : Mom d) (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) : HSt V D₀ → HSt V D₀ → Prop
  | vine (h : HSt V D₀) (K : Step1.VineCut Src.γL h.s.M) (R : ℝ) (kp : ℕ) (hR : IsLabel L γ η R) (hkp : kp = 0 ∨ kp = 50)
      (hu : h.s.cls K.C.upper = .eps) (hl : h.s.cls K.C.lower = .eps)
      (ga : ∀ k0, Adm0 k0 → GapSim L w (k0 ∘ h.s.down) K.x₁ K.x₂ R)
      (gb : ∀ k0, Adm0 k0 → GapSim L w (k0 ∘ h.s.down) K.y₁ K.y₂ R)
      (htwin : ∀ k0, Adm0 k0 → (pgap L w k0 (h.s.pr K.y₁ K.y₂) = pgap L w k0 (h.s.pr K.x₁ K.x₂) ∨
        pgap L w k0 (h.s.pr K.y₁ K.y₂) = -pgap L w k0 (h.s.pr K.x₁ K.x₂)))
      (hι : kp = 50 → IotaUnif Adm0 L η w h (h.s.pr K.x₁ K.x₂) R)
      (hι0 : kp = 0 → ∀ k0, Adm0 k0 → ¬ IotaHit L η w k0 h.alive (h.s.pr K.x₁ K.x₂) R ∧
        ¬ IotaHit L η w k0 (h.s.pr K.x₁ K.x₂ :: h.alive) (h.s.pr K.y₁ K.y₂) R)
      (hsg : ∀ k0, Adm0 k0 → Molecule.gapKind L γ η (Molecule.gapAt L w (k0 ∘ h.s.down) K.x₁ K.x₂) = .SG)
      (h3a : 3 ≤ h.s.M.deg K.C.upper) (h3b : 3 ≤ h.s.M.deg K.C.lower) :
      UStep1 L γ η w Adm0 h (h.vinePostL K R kp)

variable {L γ η : ℝ} {w : Mom d} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {κ : D₀ → (Fin d → ℤ)}

theorem UStep1.hstep {h h' : HSt V D₀} (hs : UStep1 L γ η w Adm0 h h') (hk : Adm0 κ) : HStep1 L γ η w κ h h' := by
  cases hs with
  | vine K R kp hR hkp hu hl ga gb htwin hι hι0 hsg h3a h3b =>
    refine HStep1.vine h K R kp hR hkp hu hl (ga κ hk) (gb κ hk) (htwin κ hk) ?_ ?_ (hsg κ hk) h3a h3b
    · refine ⟨fun h50 => (hι h50).hit hk, fun hit => ?_⟩
      by_contra hne
      rcases hkp with h0 | h50
      · exact (hι0 h0 κ hk).1 hit
      · exact hne h50
    · refine ⟨fun h50 => ?_, fun hit => ?_⟩
      · have h1 := (hι h50).hit hk
        exact iotaHit_twin (h1.mono fun q hq => List.mem_cons_of_mem _ hq) (htwin κ hk)
      · by_contra hne
        rcases hkp with h0 | h50
        · exact (hι0 h0 κ hk).2 hit
        · exact hne h50

end WaveTurbulence.GammaLow.FinalCount.H
