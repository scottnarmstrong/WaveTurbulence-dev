/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafDerivativeProfileBounds
public import WaveTurbulence.Foundations.Spine.LeafwiseKernelSpatial
/-! Uniform finite-order bounds for every leaf-derivative assignment, used for normal convergence. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct

noncomputable def leafDerivativeCosts {w d : ℕ} (C : (Fin w × TTree.Path) → NNReal)
    (A : ℕ) (word : List (Fin d)) : (Fin w × TTree.Path) → NNReal :=
  fun a => (d : NNReal) ^ (A + word.length) * C a

theorem leafDerivativeProfiles_norm {w d A B : ℕ} (hd : 1 ≤ d)
    (G : Garden w) (H : LeafProfiles w d) (word : List (Fin d))
    (c : LeafDerivativeChoices G word.length) (C : (Fin w × TTree.Path) → NNReal)
    (hc : ∀ l ∈ inputLeaves G, ContDiff ℝ (A + word.length : ℕ) (H l.1))
    (hb : ∀ l ∈ inputLeaves G, SNormR (A + word.length) B (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ)) :
    ∀ l ∈ inputLeaves G, SNormR A B (leafDerivativeProfiles G H word c l.1) ≤
      ENNReal.ofReal (leafDerivativeCosts C A word l.1 : ℝ) := by
  intro l hl
  let a : ActualInputLeaves G := ⟨l, hl⟩
  have hh := SNormR_leafDerivativeProfiles_bound hd G H word c a (hc l hl)
    (C l.1 : ℝ) (NNReal.coe_nonneg _) (hb l hl)
  simpa only [leafDerivativeCosts, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast] using hh

theorem contDiff_leafDerivative_kernel {w d B : ℕ} (hd : 1 ≤ d) {L : ℝ} (hL : 1 ≤ L)
    (hB : d + 1 ≤ B) (γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (word : List (Fin d)) (c : LeafDerivativeChoices LG.garden word.length)
    (C : (Fin w × TTree.Path) → NNReal)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (1 + word.length : ℕ) (H l.1))
    (hb : ∀ l ∈ inputLeaves LG.garden, SNormR (1 + word.length) B (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ))
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (Finset.univ.filter fun l : GLeaf LG.garden.tree =>
      l.1.1 = j ∧ LG.garden.IsLone l).card ≤ 1) :
    ContDiff ℝ (1 : ℕ) (fun k =>
      kernelLeaves L γ δ LG (leafDerivativeProfiles LG.garden H word c) up s k nroot nfl) := by
  have hreal := contDiff_leafDerivativeProfiles LG.garden H word c hc
  have hcomplex := fun l hl => Complex.ofRealCLM.contDiff.comp (hreal l hl)
  exact contDiff_kernelLeaves_spatial hd hL γ δ LG _ (leafDerivativeCosts C 1 word)
    hcomplex (leafDerivativeProfiles_norm hd LG.garden H word c C hc hb) hB up s nroot nfl hlone

end WaveTurbulence.LGSpine
