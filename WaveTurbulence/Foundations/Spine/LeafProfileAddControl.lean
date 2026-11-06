/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseKernel
public import WaveTurbulence.Foundations.XChain.SNormAddBounds
public import WaveTurbulence.Foundations.Spine.NormAssembly
/-! Actual individual-leaf spatial control is stable under adding phi and the remainder. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct

 theorem LeafwiseControlled.add {w d : ℕ} (hd : 1 ≤ d) (LG : LayeredGarden w)
    (H₀ H₁ : LeafProfiles w d) (B₀ B₁ : (Fin w × TTree.Path) → NNReal)
    (h₀ : LeafwiseControlled LG H₀ B₀) (h₁ : LeafwiseControlled LG H₁ B₁) :
    LeafwiseControlled LG (fun a x => H₀ a x + H₁ a x) (fun a => B₀ a + B₁ a) := by
  intro l hl
  have hne : 40 * d ≠ 0 := by omega
  have hc₀ := contDiff_of_SNorm_bound hne (fun x => (H₀ l.1 x : ℂ)) (B₀ l.1) (h₀ l hl)
  have hc₁ := contDiff_of_SNorm_bound hne (fun x => (H₁ l.1 x : ℂ)) (B₁ l.1) (h₁ l hl)
  have hh := SNorm_add_bound (fun x => (H₀ l.1 x : ℂ)) (fun x => (H₁ l.1 x : ℂ)) hc₀ hc₁
    (B₀ l.1) (B₁ l.1) (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) (h₀ l hl) (h₁ l hl)
  change SNorm (40 * d) (40 * d) (fun x => ((H₀ l.1 x + H₁ l.1 x : ℝ) : ℂ)) ≤ _
  have he : (fun x => ((H₀ l.1 x + H₁ l.1 x : ℝ) : ℂ)) =
      (fun x => (H₀ l.1 x : ℂ)) + (fun x => (H₁ l.1 x : ℂ)) := by
    funext x
    exact Complex.ofReal_add _ _
  rw [he]
  simpa only [NNReal.coe_add] using hh

end WaveTurbulence.LGSpine
