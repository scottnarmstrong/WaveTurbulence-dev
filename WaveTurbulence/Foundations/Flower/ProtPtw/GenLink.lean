/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltSrc.Spectral

/-! # D6a PROT-PTW: literal link sums with a general lattice weight

o82 Prop 14.2 inserts, besides the upper filters of Lemma 14.1 (functions of `⟨x, y⟩`), a bounded multiplier `R_E` of
the exceptional link variables (the dagger, the selected reciprocal). Here a link carries an arbitrary weight
`ψ : (ℤ^d)² → ℂ` of its lattice pair. With `ψ = φ ∘ ⟨·,·⟩` it is D5a's filtered link (`rfl`). The array summand
factors exactly as main's (`tsum_genLinkArraySummand`), and the trivial bound is `sup ‖ψ‖ · (5L)^{2d}`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPtw
open WaveTurbulence.Incoh WaveTurbulence.Flower.FiltLink

variable {d : ℕ}

/-- A lattice pair of one link. -/
abbrev LPair (d : ℕ) : Type := (Fin d → ℤ) × (Fin d → ℤ)

/-- The literal link sum with a general weight of the lattice pair. -/
def genLinkLatticeSum (L s : ℝ) (A : LinkParameters d) (ψ : LPair d → ℂ) : ℂ :=
  ∑' p, linkAmplitude L A p * ψ p * WeylSums.e (linkPhase L s A p)

/-- The time factor of a link with a general weight. -/
def genLinkTimeFactor (L γ δ : ℝ) (Q : LayerLink d) (ψ : LPair d → ℂ) (t : Fin 2 → ℝ) : ℂ :=
  genLinkLatticeSum L (((Q.orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) * (t 0 - t 1)) Q.toLinkParameters ψ

theorem genLinkTimeFactor_bilinear (L γ δ : ℝ) (Q : LayerLink d) (φ : ℝ → ℂ) (t : Fin 2 → ℝ) :
    genLinkTimeFactor L γ δ Q (fun p => φ (linkBilinear L p)) t = filtLinkTimeFactor L γ δ Q φ t := rfl

theorem finite_support_genAmplitude {L : ℝ} (hL : 0 < L) (A : LinkParameters d) (ψ : LPair d → ℂ) :
    (Function.support (fun p => linkAmplitude L A p * ψ p)).Finite := by
  apply (finite_support_linkAmplitude hL A).subset
  intro p hp hz
  exact hp (by simp only [hz, zero_mul])

theorem continuous_genLinkLatticeSum_shifts {X : Type*} [TopologicalSpace X] {L : ℝ} (hL : 0 < L)
    (c₁ c₂ : Mom d) (ψ : LPair d → ℂ) {s : X → ℝ} {ξ ζ : X → Mom d} (hs : Continuous s) (hξ : Continuous ξ)
    (hζ : Continuous ζ) :
    Continuous (fun x => genLinkLatticeSum L (s x)
      { leftCenter := c₁, rightCenter := c₂, leftShift := ξ x, rightShift := ζ x } ψ) :=
  WeylSums.continuous_finite_amplitude_sum
    (fun p => linkAmplitude L { leftCenter := c₁, rightCenter := c₂, leftShift := 0, rightShift := 0 } p * ψ p)
    (finite_support_genAmplitude hL _ ψ)
    (fun x p => linkPhase L (s x) { leftCenter := c₁, rightCenter := c₂, leftShift := ξ x, rightShift := ζ x } p)
    (fun _ => by unfold linkPhase; fun_prop)

theorem continuous_genLinkLatticeSum {L : ℝ} (hL : 0 < L) (A : LinkParameters d) (ψ : LPair d → ℂ) :
    Continuous (fun s => genLinkLatticeSum L s A ψ) :=
  WeylSums.continuous_finite_amplitude_sum _ (finite_support_genAmplitude hL A ψ)
    (fun s p => linkPhase L s A p) (fun _ => by unfold linkPhase; fun_prop)

theorem continuous_genLinkTimeFactor {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : LayerLink d) (ψ : LPair d → ℂ) :
    Continuous (genLinkTimeFactor L γ δ Q ψ) :=
  (continuous_genLinkLatticeSum hL Q.toLinkParameters ψ).comp (by fun_prop)

theorem norm_genLinkTerm_le (L s : ℝ) (A : LinkParameters d) (ψ : LPair d → ℂ) {B : ℝ}
    (hψ : ∀ p, ‖ψ p‖ ≤ B) (p : LPair d) :
    ‖linkAmplitude L A p * ψ p * WeylSums.e (linkPhase L s A p)‖ ≤ B * ‖cutoffAmplitude L A p‖ := by
  rw [mul_right_comm, norm_mul]
  calc
    _ ≤ ‖cutoffAmplitude L A p‖ * B :=
      mul_le_mul (norm_linkTerm_le L s A p) (hψ _) (norm_nonneg _) (norm_nonneg _)
    _ = _ := mul_comm _ _

/-- The trivial supremum: `‖ψ‖_∞ (5L)^{2d}`, uniformly in centers, shifts and the time frequency. -/
theorem norm_genLinkLatticeSum_le {L : ℝ} (hL : 1 ≤ L) (s : ℝ) (A : LinkParameters d)
    (ψ : LPair d → ℂ) {B : ℝ} (hB : 0 ≤ B) (hψ : ∀ p, ‖ψ p‖ ≤ B) :
    ‖genLinkLatticeSum L s A ψ‖ ≤ B * (5 * L) ^ (2 * d) := by
  have hLp := zero_lt_one.trans_le hL
  have hsum : Summable (fun p => ‖linkAmplitude L A p * ψ p * WeylSums.e (linkPhase L s A p)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_genLinkTerm_le L s A ψ hψ)
      ((summable_norm_cutoffAmplitude hLp A).mul_left B)
  apply (norm_tsum_le_tsum_norm hsum).trans
  apply (Summable.tsum_le_tsum (norm_genLinkTerm_le L s A ψ hψ) hsum
    ((summable_norm_cutoffAmplitude hLp A).mul_left B)).trans
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (tsum_norm_cutoffAmplitude_le hL A) hB

theorem norm_genLinkTimeFactor_le {L : ℝ} (hL : 1 ≤ L) (γ δ : ℝ) (Q : LayerLink d)
    (ψ : LPair d → ℂ) {B : ℝ} (hB : 0 ≤ B) (hψ : ∀ p, ‖ψ p‖ ≤ B) (t : Fin 2 → ℝ) :
    ‖genLinkTimeFactor L γ δ Q ψ t‖ ≤ B * (5 * L) ^ (2 * d) :=
  norm_genLinkLatticeSum_le hL _ _ ψ hB hψ

/-! ### Arrays -/

/-- The weight of a link array: the product of the per-link weights. -/
def arrayWeight {n : ℕ} (ψ : Fin n → LPair d → ℂ) (p : (Fin n × Fin 2) → Fin d → ℤ) : ℂ :=
  ∏ i, ψ i (p (i, 0), p (i, 1))

theorem norm_arrayWeight_le {n : ℕ} (ψ : Fin n → LPair d → ℂ) {B : ℝ} (_hB : 0 ≤ B)
    (hψ : ∀ i q, ‖ψ i q‖ ≤ B) (p : (Fin n × Fin 2) → Fin d → ℤ) : ‖arrayWeight ψ p‖ ≤ B ^ n := by
  unfold arrayWeight
  rw [norm_prod]
  calc
    _ ≤ ∏ _i : Fin n, B := by gcongr with i; exact hψ i _
    _ = B ^ n := by simp

/-- The weighted analytic link-array summand. -/
def genLinkArraySummand {n : ℕ} (L γ δ : ℝ) (Q : Fin n → LayerLink d) (ψ : Fin n → LPair d → ℂ)
    (t : Fin n → Fin 2 → ℝ) (p : (Fin n × Fin 2) → Fin d → ℤ) : ℂ :=
  ∏ i, linkAmplitude L (Q i).toLinkParameters (p (i, 0), p (i, 1)) * ψ i (p (i, 0), p (i, 1)) *
    WeylSums.e (linkPhase L ((((Q i).orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) *
      (t i 0 - t i 1)) (Q i).toLinkParameters (p (i, 0), p (i, 1)))

theorem genLinkArraySummand_eq {n : ℕ} (L γ δ : ℝ) (Q : Fin n → LayerLink d) (ψ : Fin n → LPair d → ℂ)
    (t : Fin n → Fin 2 → ℝ) (p : (Fin n × Fin 2) → Fin d → ℤ) :
    genLinkArraySummand L γ δ Q ψ t p = linkArraySummand L γ δ Q t p * arrayWeight ψ p := by
  rw [genLinkArraySummand, linkArraySummand, arrayWeight, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

/-- The weighted array sum is exactly the product of the weighted link factors. -/
theorem tsum_genLinkArraySummand {n : ℕ} {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d)
    (ψ : Fin n → LPair d → ℂ) (t : Fin n → Fin 2 → ℝ) :
    (∑' p : (Fin n × Fin 2) → Fin d → ℤ, genLinkArraySummand L γ δ Q ψ t p) =
      ∏ i, genLinkTimeFactor L γ δ (Q i) (ψ i) (t i) := by
  let f := fun i : Fin n => fun p : LPair d =>
    linkAmplitude L (Q i).toLinkParameters p * ψ i p *
      WeylSums.e (linkPhase L ((((Q i).orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) *
        (t i 0 - t i 1)) (Q i).toLinkParameters p)
  have hf (i : Fin n) : (Function.support (f i)).Finite :=
    (finite_support_genAmplitude hL (Q i).toLinkParameters (ψ i)).subset
      (fun p hp hz => hp (by simp only [f, hz, zero_mul]))
  calc
    _ = ∑' p : Fin n → LPair d, ∏ i, f i (p i) :=
      (linkLatticeArrayEquiv (Fin n) (Fin d → ℤ)).tsum_eq (fun p => ∏ i, f i (p i))
    _ = ∏ i, ∑' p, f i p := WeylSums.tsum_pi_prod_of_finite_support f hf
    _ = _ := rfl

end WaveTurbulence.Flower.ProtPtw
