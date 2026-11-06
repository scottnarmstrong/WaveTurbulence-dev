/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RootModifiedProfileNorm
public import WaveTurbulence.Foundations.Spine.LeafDerivativeProfileBounds
/-! Quantitative input bounds for the exact combined coordinate-weight and derivative modifications. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct

theorem SNormR_combined_leaf_modification_bound {w d A B m : ℕ} (hd : 1 ≤ d)
    (G : Garden w) (hp : G.IsPlain) (H : LeafProfiles w d) (word : List (Fin d))
    (a : LeafDerivativeChoices G word.length) (c : RootWeightChoices G d m)
    (l : ActualInputLeaves G) (hc : ContDiff ℝ (A + word.length : ℕ) (H l.1.1))
    (C : ℝ) (hC : 0 ≤ C)
    (hb : SNormR (A + word.length) (B + 4 * m) (H l.1.1) ≤ ENNReal.ofReal C) :
    SNormR A B (rootModifiedProfiles G hp (leafDerivativeProfiles G H word a) c l.1.1) ≤
      ENNReal.ofReal ((((2 : ℝ) ^ A * (d : ℝ) ^ A) ^ (4 * m)) *
        ((d : ℝ) ^ (A + word.length) * C)) := by
  have hderiv := SNormR_leafDerivativeProfiles_bound hd G H word a l hc C hC hb
  have hreal : ContDiff ℝ A (leafDerivativeProfiles G H word a l.1.1) := by
    rw [leafDerivativeProfiles_input]
    apply contDiff_realWordD
    have hlen := assignedDerivativeWord_length G word a l
    exact hc.of_le (by exact_mod_cast Nat.add_le_add_left hlen A)
  have hcomplex := Complex.ofRealCLM.contDiff.comp hreal
  exact SNormR_rootModifiedProfile_bound hd G hp (leafDerivativeProfiles G H word a) c l
    hcomplex ((d : ℝ) ^ (A + word.length) * C) (by positivity) hderiv

end WaveTurbulence.LGSpine
