/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.WeylTensorFactors
public import WaveTurbulence.Foundations.WeylSums.LatticeBoxes
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import WaveTurbulence.Foundations.WeylSums.FourierTranslations
public import WaveTurbulence.Foundations.WeylSums.QuadraticDiagonalization
public import WaveTurbulence.Foundations.WeylSums.WeylSymmetry
public import WaveTurbulence.Foundations.WeylSums.WeylMoments
public import WaveTurbulence.Frozen.Defs.LatticePoint

/-!
# The finite quadratic lattice sums in TARGET Lemmas 5.3 and lemcubic

These definitions reproduce the tier-B1 draft sums using the frozen momentum
and lattice carriers and the landed fixed cutoff. Only Foundations names are
introduced; the orchestrator owns the bridges to the frozen anchors.
-/

public section
open Finset MeasureTheory
open scoped BigOperators
namespace WaveTurbulence.WeylSums

/-- TARGET's vector cutoff, the tensor product of the fixed scalar cutoff. -/
@[expose] noncomputable def latticeCutoff {d : ℕ} (x : Mom d) : ℝ :=
  ∏ i, Fourier.chi0 (x i)

/-- Equality with the scalar formula used in the tier-B1 drafts. -/
theorem chi0_eq_draft_formula (x : ℝ) :
    Fourier.chi0 x = Real.smoothTransition (2-2*|x|) := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, Fourier.chi0,
      Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2+2*x), mul_one]
  · have hx' : x ≤ 0 := (lt_of_not_ge hx).le
    rw [abs_of_nonpos hx', Fourier.chi0,
      Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2-2*x), one_mul]
    congr 1
    ring

/-- Only finitely many lattice points meet a translated cutoff. -/
theorem finite_latticeCutoff {d : ℕ} {L : ℝ} (hL : 0 < L) (a : Mom d) :
    {n : Fin d → ℤ | latticeCutoff (latticePoint L n-a) ≠ 0}.Finite := by
  refine (Set.finite_Icc (fun j => ⌊L*(a j-1)⌋) (fun j => ⌈L*(a j+1)⌉)).subset ?_
  intro n hn
  simp only [Set.mem_ofPred_eq, latticeCutoff, prod_ne_zero_iff, mem_univ, true_imp_iff] at hn
  have hj (j : Fin d) : |(n j : ℝ)/L-a j| < 1 := by
    by_contra hh
    exact hn j (Fourier.chi0_eq_zero (by simpa only [latticePoint, PiLp.toLp_apply, PiLp.sub_apply] using not_lt.mp hh))
  constructor
  · intro j
    have hh := (abs_lt.mp (hj j)).1
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hL] at hh
    exact Int.floor_le_iff.mpr (by exact_mod_cast (by linarith : L*(a j-1) < (n j : ℝ)+1))
  · intro j
    have hh := (abs_lt.mp (hj j)).2
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hL] at hh
    exact Int.le_ceil_iff.mpr (by exact_mod_cast (by linarith : (n j : ℝ)-1 < L*(a j+1)))

/-- The bilinear sum in TARGET Lemma 5.3 (`lemlayer2`), with no normalization. -/
@[expose] noncomputable def bilinearLatticeSum {d : ℕ} (L s : ℝ) (a b ξ ζ : Mom d) : ℂ :=
  ∑' q : (Fin d → ℤ) × (Fin d → ℤ),
    ((latticeCutoff (latticePoint L q.1-a) * latticeCutoff (latticePoint L q.2-b) : ℝ) : ℂ) *
      e (inner ℝ (latticePoint L q.1) ξ + inner ℝ (latticePoint L q.2) ζ +
        s * inner ℝ (latticePoint L q.1) (latticePoint L q.2))

/-- DH23 Lemma 6.6's weighted bilinear lattice sum, at cutoff width `width`. -/
@[expose] noncomputable def weightedBilinearLatticeSum {d : ℕ} (Φ : ℝ → Mom d → Mom d → ℂ)
    (L width s : ℝ) (a b ξ ζ : Mom d) : ℂ :=
  ∑' q : (Fin d → ℤ) × (Fin d → ℤ),
    ((latticeCutoff (width⁻¹ • (latticePoint L q.1-a)) *
      latticeCutoff (width⁻¹ • (latticePoint L q.2-b)) : ℝ) : ℂ) *
      Φ s (latticePoint L q.1) (latticePoint L q.2) *
      e (inner ℝ (latticePoint L q.1) ξ + inner ℝ (latticePoint L q.2) ζ +
        s * inner ℝ (latticePoint L q.1) (latticePoint L q.2))

/-- The two quadratic forms of TARGET's `lemcubic`; the Boolean convention
matches the tier-B1 draft exactly. -/
@[expose] noncomputable def cubicQuadraticForm {d : ℕ} (sel : Bool) (x y z : Mom d) : ℝ :=
  if sel then inner ℝ x z else inner ℝ z (x+y-z)

/-- The cubic lattice sum in TARGET `lemcubic`, with all spatial shifts. -/
@[expose] noncomputable def cubicLatticeSum {d : ℕ} (L t s : ℝ) (sel : Bool)
    (a b c ξ ζ ω : Mom d) : ℂ :=
  ∑' q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ),
    ((latticeCutoff (latticePoint L q.1-a) * latticeCutoff (latticePoint L q.2.1-b) *
      latticeCutoff (latticePoint L q.2.2-c) : ℝ) : ℂ) *
      e (t * inner ℝ (latticePoint L q.1) (latticePoint L q.2.1) +
        s * cubicQuadraticForm sel (latticePoint L q.1) (latticePoint L q.2.1) (latticePoint L q.2.2) +
        inner ℝ ξ (latticePoint L q.1) + inner ℝ ζ (latticePoint L q.2.1) +
        inner ℝ ω (latticePoint L q.2.2))

/-- Finite support of every bilinear cutoff sum, independent of its phase. -/
theorem finite_support_bilinear {d : ℕ} {L : ℝ} (hL : 0 < L) (a b : Mom d)
    (φ : (Fin d → ℤ) × (Fin d → ℤ) → ℂ) :
    (Function.support fun q =>
      ((latticeCutoff (latticePoint L q.1-a) * latticeCutoff (latticePoint L q.2-b) : ℝ) : ℂ) * φ q).Finite := by
  refine ((finite_latticeCutoff hL a).prod (finite_latticeCutoff hL b)).subset ?_
  intro q hq
  simp only [Function.mem_support, ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, not_or] at hq
  exact ⟨hq.1.1, hq.1.2⟩

/-- Finite support of every cubic cutoff sum, independent of its phase. -/
theorem finite_support_cubic {d : ℕ} {L : ℝ} (hL : 0 < L) (a b c : Mom d)
    (φ : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) → ℂ) :
    (Function.support fun q =>
      ((latticeCutoff (latticePoint L q.1-a) * latticeCutoff (latticePoint L q.2.1-b) *
        latticeCutoff (latticePoint L q.2.2-c) : ℝ) : ℂ) * φ q).Finite := by
  refine ((finite_latticeCutoff hL a).prod ((finite_latticeCutoff hL b).prod
    (finite_latticeCutoff hL c))).subset ?_
  intro q hq
  simp only [Function.mem_support, ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, not_or] at hq
  exact ⟨hq.1.1.1, hq.1.1.2, hq.1.2⟩

end WaveTurbulence.WeylSums
