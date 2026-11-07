/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepSup2

/-!
# S2 REPRESENTS, VINE-D (moments): superpositions with a frequency moment bound

R58 (F-LOWCLOCK): the time frequency of a lower-child slot at its parent clock `τ_{b_j}` becomes the modulation `λ` of the
unit `j`, and VINEEST(λ) costs `(1 + |λ|)^{6η⁶}`.  So the slot superpositions must carry the moment
`Σ_l ⟨m_l/2⟩^θ w_l ≤ μ` (`maxBracketPow θ (half m)`), which the X-norm bounds of the gates provide (`fourier_superposition`,
`fourier_centre_superposition` give exactly this weighted sum).  `SupM θ`, `CenSupM θ`: `Sup`, `CenSup` with the weighted
mass; they imply the plain ones (`maxBracketPow ≥ 1`).  `exists_cenSupM`, `exists_supM`: the producers from `XNormRestr`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.LGSpine
open scoped ENNReal

variable {d r : ℕ}

/-- Time-Fourier superposition of unit amplitudes with `θ`-weighted total weight `≤ μ`. -/
def SupM (θ : ℝ) (A : ℕ) (B : Set (Fin r → ℝ)) (f : (Fin r → ℝ) → Mom d → ℂ) (μ : ℝ≥0∞) : Prop :=
  ∃ (Λ : Type) (_ : Countable Λ) (w : Λ → ℝ) (m : Λ → Fin r → ℤ) (a : Λ → Mom d → ℂ),
    (∀ l, 0 ≤ w l) ∧ Summable w ∧ (∀ l, SNorm A 0 (a l) ≤ 1) ∧
    (∀ t ∈ B, ∀ k, HasSum (fun l => (w l : ℂ) * a l k * fsPhase (m l) t) (f t k)) ∧
    ∑' l, maxBracketPow θ (half (m l)) * ENNReal.ofReal (w l) ≤ μ

/-- The same with unit-ball centres. -/
def CenSupM (θ : ℝ) (A : ℕ) (B : Set (Fin r → ℝ)) (f : (Fin r → ℝ) → Mom d → ℂ) (μ : ℝ≥0∞) : Prop :=
  ∃ (Λ : Type) (_ : Countable Λ) (w : Λ → ℝ) (m : Λ → Fin r → ℤ) (n : Λ → Fin d → ℤ)
    (a : Λ → Mom d → ℂ),
    (∀ l, 0 ≤ w l) ∧ Summable w ∧ (∀ l, SNorm A 0 (a l) ≤ 1) ∧
    (∀ l k, a l k ≠ 0 → ‖k - latPt d (n l)‖ ≤ 1) ∧
    (∀ t ∈ B, ∀ k, HasSum (fun l => (w l : ℂ) * a l k * fsPhase (m l) t) (f t k)) ∧
    ∑' l, maxBracketPow θ (half (m l)) * ENNReal.ofReal (w l) ≤ μ

theorem SupM.toSup {θ : ℝ} (hθ : 0 ≤ θ) {A : ℕ} {B : Set (Fin r → ℝ)} {f : (Fin r → ℝ) → Mom d → ℂ}
    {μ : ℝ≥0∞} (h : SupM θ A B f μ) : Sup A B f μ := by
  obtain ⟨Λ, hc, w, m, a, h1, h2, h3, h4, h5⟩ := h
  refine ⟨Λ, hc, w, m, a, h1, h2, h3, h4, le_trans (ENNReal.tsum_le_tsum fun l => ?_) h5⟩
  exact le_mul_of_one_le_left bot_le (RepAnalytic.one_le_maxBracketPow hθ _)

theorem CenSupM.toCenSup {θ : ℝ} (hθ : 0 ≤ θ) {A : ℕ} {B : Set (Fin r → ℝ)} {f : (Fin r → ℝ) → Mom d → ℂ}
    {μ : ℝ≥0∞} (h : CenSupM θ A B f μ) : CenSup A B f μ := by
  obtain ⟨Λ, hc, w, m, n, a, h1, h2, h3, h3', h4, h5⟩ := h
  refine ⟨Λ, hc, w, m, n, a, h1, h2, h3, h3', h4, le_trans (ENNReal.tsum_le_tsum fun l => ?_) h5⟩
  exact le_mul_of_one_le_left bot_le (RepAnalytic.one_le_maxBracketPow hθ _)

theorem SupM.mono {θ : ℝ} {A : ℕ} {B : Set (Fin r → ℝ)} {f : (Fin r → ℝ) → Mom d → ℂ} {μ μ' : ℝ≥0∞}
    (h : SupM θ A B f μ) (hμ : μ ≤ μ') : SupM θ A B f μ' := by
  obtain ⟨Λ, hc, w, m, a, h1, h2, h3, h4, h5⟩ := h
  exact ⟨Λ, hc, w, m, a, h1, h2, h3, h4, h5.trans hμ⟩

theorem CenSupM.mono {θ : ℝ} {A : ℕ} {B : Set (Fin r → ℝ)} {f : (Fin r → ℝ) → Mom d → ℂ} {μ μ' : ℝ≥0∞}
    (h : CenSupM θ A B f μ) (hμ : μ ≤ μ') : CenSupM θ A B f μ' := by
  obtain ⟨Λ, hc, w, m, n, a, h1, h2, h3, h3', h4, h5⟩ := h
  exact ⟨Λ, hc, w, m, n, a, h1, h2, h3, h3', h4, h5.trans hμ⟩

theorem SupM.zero (θ : ℝ) (A : ℕ) (B : Set (Fin r → ℝ)) (f : (Fin r → ℝ) → Mom d → ℂ)
    (hf : ∀ t ∈ B, ∀ k, f t k = 0) (μ : ℝ≥0∞) : SupM θ A B f μ :=
  ⟨Empty, inferInstance, fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim,
    (hasSum_fintype _).summable, fun e => e.elim,
    fun t ht k => by simp [hf t ht k], by simp⟩

theorem CenSupM.zero (θ : ℝ) (A : ℕ) (B : Set (Fin r → ℝ)) (f : (Fin r → ℝ) → Mom d → ℂ)
    (hf : ∀ t ∈ B, ∀ k, f t k = 0) (μ : ℝ≥0∞) : CenSupM θ A B f μ :=
  ⟨Empty, inferInstance, fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim,
    fun e => e.elim, (hasSum_fintype _).summable, fun e => e.elim, fun e => e.elim,
    fun t ht k => by simp [hf t ht k], by simp⟩

/-- Centred superposition with moment of a function with `XNormRestr ≤ X` (`Λ₂ > d`). -/
theorem exists_cenSupM (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 ≤ θ) {Λ₁ Λ₂ : ℕ} (hΛ₁ : Λ₁ ≠ 0) (hΛ₂ : d < Λ₂) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (q : Fin r → ℝ) (B : Set (Fin r → ℝ)) (f : (Fin r → ℝ) → Mom d → ℂ)
      (X : ℝ≥0∞), X ≠ ⊤ → B ⊆ cell q → B ⊆ closure (interior B) →
      (∀ k, Continuous fun t => f t k) → XNormRestr θ Λ₁ Λ₂ B Set.univ f ≤ X →
      CenSupM θ Λ₁ B f (C * X) := by
  obtain ⟨C, hC, h⟩ := fourier_centre_superposition (r := r) (d := d) hd hθ hΛ₁ hΛ₂
  refine ⟨2 * C, ENNReal.mul_ne_top (by simp) hC, fun q B f X hX hBc hBi hfc hn => ?_⟩
  by_cases hX0 : X = 0
  · subst hX0
    exact CenSupM.zero θ _ _ _ (f_eq_zero_of_xnorm_zero hθ Λ₁ Λ₂ hBi hfc hn) _
  · have hlt : XNormRestr θ Λ₁ Λ₂ B Set.univ f < 2 * X := by
      calc _ ≤ X := hn
        _ < X + X := ENNReal.lt_add_right hX hX0
        _ = 2 * X := (two_mul X).symm
    obtain ⟨w, a, h1, h2, h3, h4, h5, h6⟩ :=
      h q B Set.univ f (2 * X) (ENNReal.mul_ne_top (by simp) hX) hBc hBi (fun k _ => hfc k) hlt
    exact ⟨(Fin r → ℤ) × (Fin d → ℤ), inferInstance, w, Prod.fst, Prod.snd, a, h1, h5, h2, h3,
      fun t ht k => h4 t ht k (Set.mem_univ _), h6.trans (le_of_eq (by ring))⟩

/-- Superposition with moment (no centres) of a function with `XNormRestr ≤ X`. -/
theorem exists_supM {θ : ℝ} (hθ : 0 ≤ θ) {Λ₁ : ℕ} (hΛ₁ : Λ₁ ≠ 0) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (q : Fin r → ℝ) (B : Set (Fin r → ℝ)) (f : (Fin r → ℝ) → Mom d → ℂ)
      (X : ℝ≥0∞), X ≠ ⊤ → B ⊆ cell q → B ⊆ closure (interior B) →
      (∀ k, Continuous fun t => f t k) → XNormRestr θ Λ₁ 0 B Set.univ f ≤ X →
      SupM θ Λ₁ B f (C * X) := by
  obtain ⟨C, hC, h⟩ := fourier_superposition (r := r) (d := d) hθ hΛ₁ (Λ₂ := 0)
  refine ⟨2 * C, ENNReal.mul_ne_top (by simp) hC, fun q B f X hX hBc hBi hfc hn => ?_⟩
  by_cases hX0 : X = 0
  · subst hX0
    exact SupM.zero θ _ _ _ (f_eq_zero_of_xnorm_zero hθ Λ₁ 0 hBi hfc hn) _
  · have hlt : XNormRestr θ Λ₁ 0 B Set.univ f < 2 * X := by
      calc _ ≤ X := hn
        _ < X + X := ENNReal.lt_add_right hX hX0
        _ = 2 * X := (two_mul X).symm
    obtain ⟨w, a, h1, h2, h3, h4, h5⟩ :=
      h q B Set.univ f (2 * X) (ENNReal.mul_ne_top (by simp) hX) hBc hBi (fun k _ => hfc k) hlt
    exact ⟨Fin r → ℤ, inferInstance, w, id, a, h1, h4, h2, fun t ht k => h3 t ht k (Set.mem_univ _),
      h5.trans (le_of_eq (by ring))⟩

end WaveTurbulence.Represents
