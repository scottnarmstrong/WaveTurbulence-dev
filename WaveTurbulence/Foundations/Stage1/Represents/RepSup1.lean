/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RepAnalytic.LeafSuperposition
public import WaveTurbulence.Foundations.Stage1.RepAnalytic.TimeFS00Main
import Mathlib.Tactic

/-!
# S2 REPRESENTS: superposition predicates for one replacement slot

`CenSup A B f μ` : on the time set `B`, the momentum function `f(t, k)` is a countable superposition
`∑_l w_l a_l(k) e^{πi m_l·t}` of unit amplitudes (`𝔖^{A,0}` norm `≤ 1`) supported in unit balls around
lattice centres, with total weight `≤ μ`.  `Sup` is the same without centres.  Closed under sums and
monotone in the mass; both are produced from `XNormRestr` bounds by `RepAnalytic`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open scoped ENNReal

variable {d r : ℕ}

/-- Time-Fourier superposition of unit amplitudes with total weight `≤ μ`. -/
def Sup (A : ℕ) (B : Set (Fin r → ℝ)) (f : (Fin r → ℝ) → Mom d → ℂ) (μ : ℝ≥0∞) : Prop :=
  ∃ (Λ : Type) (_ : Countable Λ) (w : Λ → ℝ) (m : Λ → Fin r → ℤ) (a : Λ → Mom d → ℂ),
    (∀ l, 0 ≤ w l) ∧ Summable w ∧ (∀ l, SNorm A 0 (a l) ≤ 1) ∧
    (∀ t ∈ B, ∀ k, HasSum (fun l => (w l : ℂ) * a l k * fsPhase (m l) t) (f t k)) ∧
    ∑' l, ENNReal.ofReal (w l) ≤ μ

/-- The same with unit-ball centres. -/
def CenSup (A : ℕ) (B : Set (Fin r → ℝ)) (f : (Fin r → ℝ) → Mom d → ℂ) (μ : ℝ≥0∞) : Prop :=
  ∃ (Λ : Type) (_ : Countable Λ) (w : Λ → ℝ) (m : Λ → Fin r → ℤ) (n : Λ → Fin d → ℤ)
    (a : Λ → Mom d → ℂ),
    (∀ l, 0 ≤ w l) ∧ Summable w ∧ (∀ l, SNorm A 0 (a l) ≤ 1) ∧
    (∀ l k, a l k ≠ 0 → ‖k - latPt d (n l)‖ ≤ 1) ∧
    (∀ t ∈ B, ∀ k, HasSum (fun l => (w l : ℂ) * a l k * fsPhase (m l) t) (f t k)) ∧
    ∑' l, ENNReal.ofReal (w l) ≤ μ

theorem CenSup.sup {A : ℕ} {B : Set (Fin r → ℝ)} {f : (Fin r → ℝ) → Mom d → ℂ} {μ : ℝ≥0∞}
    (h : CenSup A B f μ) : Sup A B f μ := by
  obtain ⟨Λ, hc, w, m, n, a, h1, h2, h3, -, h5, h6⟩ := h
  exact ⟨Λ, hc, w, m, a, h1, h2, h3, h5, h6⟩

theorem Sup.mono {A : ℕ} {B : Set (Fin r → ℝ)} {f : (Fin r → ℝ) → Mom d → ℂ} {μ μ' : ℝ≥0∞}
    (h : Sup A B f μ) (hμ : μ ≤ μ') : Sup A B f μ' := by
  obtain ⟨Λ, hc, w, m, a, h1, h2, h3, h4, h5⟩ := h
  exact ⟨Λ, hc, w, m, a, h1, h2, h3, h4, h5.trans hμ⟩

theorem CenSup.mono {A : ℕ} {B : Set (Fin r → ℝ)} {f : (Fin r → ℝ) → Mom d → ℂ} {μ μ' : ℝ≥0∞}
    (h : CenSup A B f μ) (hμ : μ ≤ μ') : CenSup A B f μ' := by
  obtain ⟨Λ, hc, w, m, n, a, h1, h2, h3, h3', h4, h5⟩ := h
  exact ⟨Λ, hc, w, m, n, a, h1, h2, h3, h3', h4, h5.trans hμ⟩

theorem Sup.congr {A : ℕ} {B : Set (Fin r → ℝ)} {f g : (Fin r → ℝ) → Mom d → ℂ} {μ : ℝ≥0∞}
    (h : Sup A B f μ) (hfg : ∀ t ∈ B, ∀ k, f t k = g t k) : Sup A B g μ := by
  obtain ⟨Λ, hc, w, m, a, h1, h2, h3, h4, h5⟩ := h
  exact ⟨Λ, hc, w, m, a, h1, h2, h3, fun t ht k => by rw [← hfg t ht k]; exact h4 t ht k, h5⟩

theorem CenSup.congr {A : ℕ} {B : Set (Fin r → ℝ)} {f g : (Fin r → ℝ) → Mom d → ℂ} {μ : ℝ≥0∞}
    (h : CenSup A B f μ) (hfg : ∀ t ∈ B, ∀ k, f t k = g t k) : CenSup A B g μ := by
  obtain ⟨Λ, hc, w, m, n, a, h1, h2, h3, h3', h4, h5⟩ := h
  exact ⟨Λ, hc, w, m, n, a, h1, h2, h3, h3', fun t ht k => by rw [← hfg t ht k]; exact h4 t ht k, h5⟩

theorem Sup.zero (A : ℕ) (B : Set (Fin r → ℝ)) (f : (Fin r → ℝ) → Mom d → ℂ)
    (hf : ∀ t ∈ B, ∀ k, f t k = 0) (μ : ℝ≥0∞) : Sup A B f μ :=
  ⟨Empty, inferInstance, fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim,
    (hasSum_fintype _).summable, fun e => e.elim,
    fun t ht k => by simp [hf t ht k], by simp⟩

theorem CenSup.zero (A : ℕ) (B : Set (Fin r → ℝ)) (f : (Fin r → ℝ) → Mom d → ℂ)
    (hf : ∀ t ∈ B, ∀ k, f t k = 0) (μ : ℝ≥0∞) : CenSup A B f μ :=
  ⟨Empty, inferInstance, fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim,
    fun e => e.elim, (hasSum_fintype _).summable, fun e => e.elim, fun e => e.elim,
    fun t ht k => by simp [hf t ht k], by simp⟩

theorem Sup.add {A : ℕ} {B : Set (Fin r → ℝ)} {f g : (Fin r → ℝ) → Mom d → ℂ} {μ ν : ℝ≥0∞}
    (hf : Sup A B f μ) (hg : Sup A B g ν) : Sup A B (fun t k => f t k + g t k) (μ + ν) := by
  obtain ⟨Λ, hc, w, m, a, h1, h2, h3, h4, h5⟩ := hf
  obtain ⟨Λ', hc', w', m', a', h1', h2', h3', h4', h5'⟩ := hg
  refine ⟨Λ ⊕ Λ', inferInstance, Sum.elim w w', Sum.elim m m', Sum.elim a a',
    ?_, ?_, ?_, ?_, ?_⟩
  · rintro (l | l) <;> simp [h1, h1']
  · exact Summable.sum _ h2 h2'
  · rintro (l | l) <;> simp [h3, h3']
  · intro t ht k
    exact HasSum.sum (f := fun l : Λ ⊕ Λ' => ((Sum.elim w w' l : ℝ) : ℂ) * Sum.elim a a' l k *
      fsPhase (Sum.elim m m' l) t) (h4 t ht k) (h4' t ht k)
  · rw [Summable.tsum_sum (f := fun l : Λ ⊕ Λ' => ENNReal.ofReal (Sum.elim w w' l))
      ENNReal.summable ENNReal.summable]
    exact add_le_add h5 h5'

end WaveTurbulence.Represents
