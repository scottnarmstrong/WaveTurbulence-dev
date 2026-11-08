/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Incoh.OneLinkDecay
public import WaveTurbulence.Foundations.Incoh.LinkPhaseExpansion
public import WaveTurbulence.Foundations.Incoh.RootEnvelopeMass
/-! # D5a FILT-LINK: filtered literal link factors (o82 §14)

The literal link of main's incoherent chain (`Incoh.linkLatticeSum`, TARGET (incohproof10)), with a multiplier `φ`
of the bilinear link frequency `u = ⟨x, y⟩` inserted in every lattice term (o82 Lemma 14.1's `A_H`). An upper
filter or annular factor of a linked branch `b` is a function of `|Ω_b| = 2|⟨x, y⟩|` (IncohInst `omegaNode_eq`),
so the filters of one link are such a multiplier (`Flower.FiltLink.linkFiltMult`).

This file: the filtered sum, time factor, absolute link mass and phase coefficients; `φ ≡ 1` gives main's objects
literally; continuity; the trivial supremum `‖φ‖_∞ (5L)^{2d}`; the finite phase expansion. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace WaveTurbulence.Flower.FiltLink
open WaveTurbulence.Incoh

variable {d : ℕ}

/-- The bilinear link frequency `⟨x, y⟩` of a lattice pair (`Ω = 2⟨x, y⟩`, IncohInst `omegaNode_eq`). -/
def linkBilinear (L : ℝ) (p : (Fin d → ℤ) × (Fin d → ℤ)) : ℝ :=
  inner ℝ (latticePoint L p.1) (latticePoint L p.2)

/-- **The filtered literal link sum** `A_φ(s)` (o82 Lemma 14.1, `A_H`): main's `linkLatticeSum` (with its Wick
exclusion factor) with the multiplier `φ (⟨x, y⟩)` in every lattice term. -/
def filtLinkLatticeSum (L s : ℝ) (A : LinkParameters d) (φ : ℝ → ℂ) : ℂ :=
  ∑' p, linkAmplitude L A p * φ (linkBilinear L p) * WeylSums.e (linkPhase L s A p)

/-- The filtered time factor (main's `linkTimeFactor` with the multiplier). -/
def filtLinkTimeFactor (L γ δ : ℝ) (Q : LayerLink d) (φ : ℝ → ℂ) (t : Fin 2 → ℝ) : ℂ :=
  filtLinkLatticeSum L (((Q.orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) * (t 0 - t 1)) Q.toLinkParameters φ

/-- The filtered absolute link mass (main's `layerLinkMass` with the multiplier): the pair mass of (14.1). -/
def filtLayerLinkMass (L lam : ℝ) (Q : LayerLink d) (φ : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ t in linkBox Q,
    ‖filtLinkLatticeSum L (((Q.orientation : ℤ) : ℝ) * lam * (t 0 - t 1)) Q.toLinkParameters φ‖ₑ

/-- The filtered phase coefficients (main's `linkPhaseCoefficient` times the multiplier). -/
def filtLinkPhaseCoefficient (L : ℝ) (Q : LayerLink d) (φ : ℝ → ℂ)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) : ℂ :=
  linkPhaseCoefficient L Q p * φ (linkBilinear L p)

/-! ### `φ ≡ 1` is main's literal link -/

theorem filtLinkLatticeSum_one (L s : ℝ) (A : LinkParameters d) :
    filtLinkLatticeSum L s A (fun _ => 1) = linkLatticeSum L s A := by
  simp only [filtLinkLatticeSum, linkLatticeSum, mul_one]

theorem filtLinkTimeFactor_one (L γ δ : ℝ) (Q : LayerLink d) :
    filtLinkTimeFactor L γ δ Q (fun _ => 1) = linkTimeFactor L γ δ Q := by
  funext t
  simp only [filtLinkTimeFactor, linkTimeFactor, filtLinkLatticeSum_one]

theorem filtLayerLinkMass_one (L lam : ℝ) (Q : LayerLink d) :
    filtLayerLinkMass L lam Q (fun _ => 1) = layerLinkMass L lam Q := by
  simp only [filtLayerLinkMass, layerLinkMass, filtLinkLatticeSum_one]

theorem filtLinkPhaseCoefficient_one (L : ℝ) (Q : LayerLink d) :
    filtLinkPhaseCoefficient L Q (fun _ => 1) = linkPhaseCoefficient L Q := by
  funext p
  simp only [filtLinkPhaseCoefficient, mul_one]

/-- The filtered mass at `lam = δ L^{2γ}` is the integral of the filtered time factor. -/
theorem filtLayerLinkMass_eq (L γ δ : ℝ) (Q : LayerLink d) (φ : ℝ → ℂ) :
    filtLayerLinkMass L (δ * L ^ (2 * γ)) Q φ = ∫⁻ t in linkBox Q, ‖filtLinkTimeFactor L γ δ Q φ t‖ₑ := by
  unfold filtLayerLinkMass filtLinkTimeFactor
  congr 1
  funext t
  congr 3
  ring

/-! ### Finite support and continuity -/

theorem finite_support_filtAmplitude {L : ℝ} (hL : 0 < L) (A : LinkParameters d) (φ : ℝ → ℂ) :
    (Function.support (fun p => linkAmplitude L A p * φ (linkBilinear L p))).Finite := by
  apply (finite_support_linkAmplitude hL A).subset
  intro p hp hz
  exact hp (by simp only [hz, zero_mul])

theorem continuous_filtLinkLatticeSum {L : ℝ} (hL : 0 < L) (A : LinkParameters d) (φ : ℝ → ℂ) :
    Continuous (fun s => filtLinkLatticeSum L s A φ) :=
  WeylSums.continuous_finite_amplitude_sum _ (finite_support_filtAmplitude hL A φ)
    (fun s p => linkPhase L s A p) (fun _ => by unfold linkPhase; fun_prop)

theorem continuous_filtLinkTimeFactor {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : LayerLink d) (φ : ℝ → ℂ) :
    Continuous (filtLinkTimeFactor L γ δ Q φ) :=
  (continuous_filtLinkLatticeSum hL Q.toLinkParameters φ).comp (by fun_prop)

theorem integrableOn_filtLinkTimeFactor {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : LayerLink d)
    (φ : ℝ → ℂ) : IntegrableOn (filtLinkTimeFactor L γ δ Q φ) (linkBox Q) :=
  (continuous_filtLinkTimeFactor hL γ δ Q φ).integrableOn_Icc

/-- Joint continuity in the time frequency and the Fourier shifts, at fixed centers (the filtered form of main's
`MomentumTreeData.continuous_spectral_linkTimeFactor`, whose spectral links move only the shifts). -/
theorem continuous_filtLinkLatticeSum_shifts {X : Type*} [TopologicalSpace X] {L : ℝ} (hL : 0 < L)
    (c₁ c₂ : Mom d) (φ : ℝ → ℂ) {s : X → ℝ} {ξ ζ : X → Mom d} (hs : Continuous s) (hξ : Continuous ξ)
    (hζ : Continuous ζ) :
    Continuous (fun x => filtLinkLatticeSum L (s x)
      { leftCenter := c₁, rightCenter := c₂, leftShift := ξ x, rightShift := ζ x } φ) :=
  WeylSums.continuous_finite_amplitude_sum
    (fun p => linkAmplitude L { leftCenter := c₁, rightCenter := c₂, leftShift := 0, rightShift := 0 } p *
      φ (linkBilinear L p))
    (finite_support_filtAmplitude hL _ φ)
    (fun x p => linkPhase L (s x) { leftCenter := c₁, rightCenter := c₂, leftShift := ξ x, rightShift := ζ x } p)
    (fun _ => by unfold linkPhase; fun_prop)

/-! ### The trivial supremum (o82 §15: "the trivial supremum remains `C L^{2d}`") -/

theorem norm_filtLinkTerm_le (L s : ℝ) (A : LinkParameters d) (φ : ℝ → ℂ) {B : ℝ}
    (hφ : ∀ u, ‖φ u‖ ≤ B) (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    ‖linkAmplitude L A p * φ (linkBilinear L p) * WeylSums.e (linkPhase L s A p)‖ ≤
      B * ‖cutoffAmplitude L A p‖ := by
  rw [mul_right_comm, norm_mul]
  calc
    _ ≤ ‖cutoffAmplitude L A p‖ * B :=
      mul_le_mul (norm_linkTerm_le L s A p) (hφ _) (norm_nonneg _) (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem summable_norm_filtLinkTerm {L : ℝ} (hL : 0 < L) (s : ℝ) (A : LinkParameters d)
    (φ : ℝ → ℂ) {B : ℝ} (hφ : ∀ u, ‖φ u‖ ≤ B) :
    Summable (fun p => ‖linkAmplitude L A p * φ (linkBilinear L p) * WeylSums.e (linkPhase L s A p)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_filtLinkTerm_le L s A φ hφ)
    ((summable_norm_cutoffAmplitude hL A).mul_left B)

/-- The filtered link is bounded by `‖φ‖_∞ (5L)^{2d}`, uniformly in centers, shifts and time frequency. -/
theorem norm_filtLinkLatticeSum_le {L : ℝ} (hL : 1 ≤ L) (s : ℝ) (A : LinkParameters d)
    (φ : ℝ → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ u, ‖φ u‖ ≤ B) :
    ‖filtLinkLatticeSum L s A φ‖ ≤ B * (5 * L) ^ (2 * d) := by
  have hLp := zero_lt_one.trans_le hL
  apply (norm_tsum_le_tsum_norm (summable_norm_filtLinkTerm hLp s A φ hφ)).trans
  apply (Summable.tsum_le_tsum (norm_filtLinkTerm_le L s A φ hφ) (summable_norm_filtLinkTerm hLp s A φ hφ)
    ((summable_norm_cutoffAmplitude hLp A).mul_left B)).trans
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (tsum_norm_cutoffAmplitude_le hL A) hB

theorem norm_filtLinkTimeFactor_le {L : ℝ} (hL : 1 ≤ L) (γ δ : ℝ) (Q : LayerLink d)
    (φ : ℝ → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ u, ‖φ u‖ ≤ B) (t : Fin 2 → ℝ) :
    ‖filtLinkTimeFactor L γ δ Q φ t‖ ≤ B * (5 * L) ^ (2 * d) :=
  norm_filtLinkLatticeSum_le hL _ _ φ hB hφ

/-- The filtered phase coefficients have absolute mass at most `‖φ‖_∞ (5L)^{2d}`. -/
theorem tsum_norm_filtLinkPhaseCoefficient_le {L : ℝ} (hL : 1 ≤ L) (Q : LayerLink d)
    (φ : ℝ → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ u, ‖φ u‖ ≤ B) :
    (∑' p, ‖filtLinkPhaseCoefficient L Q φ p‖) ≤ B * (5 * L) ^ (2 * d) := by
  have hLp := zero_lt_one.trans_le hL
  have hterm (p : (Fin d → ℤ) × (Fin d → ℤ)) : ‖filtLinkPhaseCoefficient L Q φ p‖ ≤
      B * ‖cutoffAmplitude L Q.toLinkParameters p‖ := by
    have h := norm_filtLinkTerm_le L 0 Q.toLinkParameters φ hφ p
    unfold filtLinkPhaseCoefficient linkPhaseCoefficient
    rwa [mul_right_comm]
  apply (Summable.tsum_le_tsum hterm
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
      ((summable_norm_cutoffAmplitude hLp _).mul_left B))
    ((summable_norm_cutoffAmplitude hLp _).mul_left B)).trans
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (tsum_norm_cutoffAmplitude_le hL _) hB

theorem finite_support_filtLinkPhaseCoefficient {L : ℝ} (hL : 0 < L) (Q : LayerLink d)
    (φ : ℝ → ℂ) : (Function.support (filtLinkPhaseCoefficient L Q φ)).Finite := by
  apply (finite_support_linkPhaseCoefficient hL Q).subset
  intro p hp hz
  exact hp (by simp only [filtLinkPhaseCoefficient, hz, zero_mul])

/-- The filtered mass is at most `‖φ‖_∞ (5L)^{2d}` (the box has unit volume): the trivial replacement mass. -/
theorem filtLayerLinkMass_le_trivial {L : ℝ} (hL : 1 ≤ L) (lam : ℝ) (Q : LayerLink d)
    (φ : ℝ → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ u, ‖φ u‖ ≤ B) :
    filtLayerLinkMass L lam Q φ ≤ ENNReal.ofReal (B * (5 * L) ^ (2 * d)) := by
  unfold filtLayerLinkMass
  calc
    _ ≤ ∫⁻ _t in linkBox Q, ENNReal.ofReal (B * (5 * L) ^ (2 * d)) := by
      apply lintegral_mono
      intro t
      dsimp only
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (norm_filtLinkLatticeSum_le hL _ _ φ hB hφ)
    _ = _ := by rw [setLIntegral_const, volume_linkBox, mul_one]

/-! ### The finite phase expansion (main's `linkTimeFactor_eq_phase_sum` with the multiplier) -/

theorem filtLinkTimeFactor_eq_phase_sum (L γ δ : ℝ) (Q : LayerLink d) (φ : ℝ → ℂ)
    (t : Fin 2 → ℝ) :
    filtLinkTimeFactor L γ δ Q φ t = ∑' p, filtLinkPhaseCoefficient L Q φ p *
      Complex.exp ((linkTemporalFrequency L γ δ Q p * (t 0 - t 1) : ℝ) * Complex.I) := by
  unfold filtLinkTimeFactor filtLinkLatticeSum
  apply tsum_congr
  intro p
  have he : linkPhase L (((Q.orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) * (t 0 - t 1)) Q.toLinkParameters p =
      linkPhase L 0 Q.toLinkParameters p +
        (((Q.orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) * (t 0 - t 1)) *
          inner ℝ (latticePoint L p.1) (latticePoint L p.2) := by
    unfold linkPhase
    ring
  have hfreq : 2 * Real.pi *
      ((((Q.orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) * (t 0 - t 1)) *
        inner ℝ (latticePoint L p.1) (latticePoint L p.2)) =
      linkTemporalFrequency L γ δ Q p * (t 0 - t 1) := by
    unfold linkTemporalFrequency
    ring
  rw [he, WeylSums.e_add]
  simp only [WeylSums.e, hfreq, filtLinkPhaseCoefficient, linkPhaseCoefficient]
  ring

end WaveTurbulence.Flower.FiltLink
