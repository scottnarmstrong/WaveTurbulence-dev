/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltSrc.Link
public import WaveTurbulence.Foundations.Incoh.LinkArraySummation
public import WaveTurbulence.Foundations.Incoh.CoupleExtension

/-! # D5b-1 FILT-SRC: `φ`-carrying definitions consumed by the source chain (interface)

Definition twins (with `φ : Fin n → ℝ → ℂ`, link `i` carrying `φ i`) of main's
- `Incoh.linkArraySummand` (`LinkArraySummation`), with `tsum_linkArraySummandFilt`;
- `Incoh.normalizedLinkIntegrand` (`NormalizedIntegrand`);
- `Incoh.RootCoordinates.linkDensity` (`RootDensityL1`), `RootCoordinates.localLinkDensity` (`LocalRootDensity`);
- `Incoh.RootCoordinates.coupleExtension` (`CoupleExtension`).

The source chain's measurability twins (D5B-MAP K5) state their conclusions with these objects, so they are fixed here
for D5b-2/D5b-3 (who prove their analytic lemmas). Copied by source from the main files named above (sha256 in
COPIED-SHA256SUMS); the only edit is `linkTimeFactor L γ δ (Q i) → filtLinkTimeFactor L γ δ (Q i) (φ i)` (in the summand:
the extra factor `φ i ⟨x_i, y_i⟩`). Main's `RootCoordinates.X` twins are `FiltSrc.RootCoordinates.XFilt` (no dot
notation: call them as `RootCoordinates.XFilt R …`). With `φ ≡ 1` each is main's object (`…Filt_one`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltSrc
open WaveTurbulence.Incoh WaveTurbulence.Flower.FiltLink

variable {d n : ℕ}

/-! ### `LinkArraySummation` -/

/-- The filtered compact lattice summand before summing over all links (twin of `linkArraySummand`). -/
def linkArraySummandFilt (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (t : Fin n → Fin 2 → ℝ) (p : (Fin n × Fin 2) → Fin d → ℤ) : ℂ :=
  ∏ i, linkAmplitude L (Q i).toLinkParameters (p (i, 0), p (i, 1)) *
    φ i (linkBilinear L (p (i, 0), p (i, 1))) *
    WeylSums.e (linkPhase L ((((Q i).orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) *
      (t i 0 - t i 1)) (Q i).toLinkParameters (p (i, 0), p (i, 1)))

/-- The filtered link lattice sum is exactly the product of the filtered link factors. -/
theorem tsum_linkArraySummandFilt {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (t : Fin n → Fin 2 → ℝ) :
    (∑' p : (Fin n × Fin 2) → Fin d → ℤ, linkArraySummandFilt L γ δ Q φ t p) =
      ∏ i, filtLinkTimeFactor L γ δ (Q i) (φ i) (t i) := by
  let f := fun i : Fin n => fun p : (Fin d → ℤ) × (Fin d → ℤ) =>
    linkAmplitude L (Q i).toLinkParameters p * φ i (linkBilinear L p) *
      WeylSums.e (linkPhase L ((((Q i).orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) *
        (t i 0 - t i 1)) (Q i).toLinkParameters p)
  have hf (i : Fin n) : (Function.support (f i)).Finite :=
    (finite_support_linkAmplitude hL (Q i).toLinkParameters).subset
      (fun p hp hz => hp (by simp only [f, hz, zero_mul]))
  calc
    _ = ∑' p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)), ∏ i, f i (p i) :=
      (linkLatticeArrayEquiv (Fin n) (Fin d → ℤ)).tsum_eq (fun p => ∏ i, f i (p i))
    _ = ∏ i, ∑' p, f i p := WeylSums.tsum_pi_prod_of_finite_support f hf
    _ = _ := rfl

theorem linkArraySummandFilt_one (L γ δ : ℝ) (Q : Fin n → LayerLink d) :
    linkArraySummandFilt L γ δ Q (fun _ _ => 1) = linkArraySummand L γ δ Q := by
  funext t p
  simp only [linkArraySummandFilt, linkArraySummand, mul_one]

/-! ### `NormalizedIntegrand`, root densities, couple extension -/

/-- The filtered localized product with its source coupling and time-order indicator
(twin of `normalizedLinkIntegrand`). -/
def normalizedLinkIntegrandFilt (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (I : Set (Fin n → Fin 2 → ℝ)) (t : Fin n → Fin 2 → ℝ) : ℂ :=
  (((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) : ℂ) *
    I.indicator (fun t => ∏ i, filtLinkTimeFactor L γ δ (Q i) (φ i) (t i)) t

theorem normalizedLinkIntegrandFilt_one (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) :
    normalizedLinkIntegrandFilt L γ δ Q (fun _ _ => 1) I = normalizedLinkIntegrand L γ δ Q I := by
  funext t
  simp only [normalizedLinkIntegrandFilt, normalizedLinkIntegrand, filtLinkTimeFactor_one]

/-- The filtered source root density (twin of `RootCoordinates.linkDensity`). -/
def RootCoordinates.linkDensityFilt {r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ)) :
    (Fin r → ℝ) → ℂ :=
  R.density (normalizedLinkIntegrandFilt L γ δ Q φ I)

theorem RootCoordinates.linkDensityFilt_one {r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ)) :
    RootCoordinates.linkDensityFilt R L γ δ Q (fun _ _ => 1) I = R.linkDensity L γ δ Q I := by
  simp only [RootCoordinates.linkDensityFilt, RootCoordinates.linkDensity, normalizedLinkIntegrandFilt_one]

/-- The filtered root density in clocks measured from their integer layers (twin of
`RootCoordinates.localLinkDensity`). -/
def RootCoordinates.localLinkDensityFilt {r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ))
    (t : Fin r → ℝ) : ℂ :=
  RootCoordinates.linkDensityFilt R L γ δ Q φ I (t + R.baseRootTimes Q)

theorem RootCoordinates.localLinkDensityFilt_one {r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ)) :
    RootCoordinates.localLinkDensityFilt R L γ δ Q (fun _ _ => 1) I = R.localLinkDensity L γ δ Q I := by
  funext t
  simp only [RootCoordinates.localLinkDensityFilt, RootCoordinates.localLinkDensity,
    RootCoordinates.linkDensityFilt_one]

/-- The filtered cutoff double integral in the original root clocks (twin of `RootCoordinates.coupleExtension`). -/
def RootCoordinates.coupleExtensionFilt (R : RootCoordinates n)
    (χ : ℝ → ℝ) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (I : Set (Fin n → Fin 2 → ℝ))
    (t : Fin 2 → ℝ) : ℂ :=
  Fourier.cutoffDoubleIntegral χ (RootCoordinates.localLinkDensityFilt R L γ δ Q φ I) (t - R.baseRootTimes Q)

theorem RootCoordinates.coupleExtensionFilt_one (R : RootCoordinates n)
    (χ : ℝ → ℝ) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ)) :
    RootCoordinates.coupleExtensionFilt R χ L γ δ Q (fun _ _ => 1) I = R.coupleExtension χ L γ δ Q I := by
  funext t
  simp only [RootCoordinates.coupleExtensionFilt, RootCoordinates.coupleExtension,
    RootCoordinates.localLinkDensityFilt_one]

end WaveTurbulence.Flower.FiltSrc
