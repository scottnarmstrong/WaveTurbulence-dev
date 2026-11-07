/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepH18
public import WaveTurbulence.Foundations.Stage1.Represents.RepH1
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Kernel
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-D (V1): the hinge families of the units from per-centre `𝔛^{θ,0,0}` bounds

TARGET L1965-L1969: on the hinge momenta of the unit `j`, localized to the unit balls around a lattice centre `c`, the
vine factor `K̃^{U_j}` (VINEEST, `XNorm00Restr θ (outBox D) (outSet D)` with the `sumint` order `E` of the momenta,
`K̃^{U_j}(t, k) = f(t, sumintBoundary σ_j E)`) is a time-Fourier superposition with unit amplitudes and total weight
`≤ C · M_j` (`unit_superposition`).  `exists_hingeFam` collects these into a `HingeFam`, uniformly in the centres;
the amplitudes are read in the garden order `k = sumintBoundary σ_j E` (an involution, `sumintBoundary_invol`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS3.Eng WaveTurbulence.RepAnalytic
open scoped ENNReal

/-- **Hinge families from per-centre bounds.** For every unit `j` and lattice centre tuple `c`, a `sumint` datum
`Dj j c`, an admissible momentum set `Kj j c` (in the `sumint` order) and the bound
`XNorm00Restr θ (outBox (Dj j c)) (Kj j c) (f j ∘ sumintBoundary σ_j) ≤ M j` with continuity on the cube give a
`HingeFam` whose weights at `(j, c)` sum to at most `C · M j`, superposing `f j t k` for `t ∈ outBox (Dj j c)` and
`sumintBoundary σ_j k ∈ Kj j c`. -/
theorem exists_hingeFam {θ : ℝ} (hθ : 0 ≤ θ) (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (J : Type) (Dj : J → (Fin 4 → Fin d → ℤ) → SumintDatum d)
      (Kj : J → (Fin 4 → Fin d → ℤ) → Set (Fin 4 → Mom d)) (σ : J → ℤˣ)
      (f : J → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ) (M : J → ℝ), (∀ j, 0 ≤ M j) →
      (∀ j c, ∀ E ∈ Kj j c, ContinuousOn (fun t => f j t (sumintBoundary (σ j) E)) (cubeSet (Dj j c).qOut)) →
      (∀ j c, XNorm00Restr θ (outBox (Dj j c)) (Kj j c) (fun t E => f j t (sumintBoundary (σ j) E)) ≤
        ENNReal.ofReal (M j)) →
      ∃ H : HingeFam J d, (∀ j c, ∑' l, H.w j c l ≤ C * M j) ∧
        ∀ j c, ∀ t ∈ outBox (Dj j c), ∀ k, sumintBoundary (σ j) k ∈ Kj j c →
          HasSum (fun l => (H.w j c l : ℂ) * H.a j c l k * fsPhase (H.m j c l) t) (f j t k) := by
  obtain ⟨C, hC, hsup⟩ := unit_superposition hθ d
  refine ⟨C, hC, fun J Dj Kj σ f M hM hcont hbd => ?_⟩
  have hex : ∀ j c, ∃ (w : (Fin 3 → ℤ) → ℝ) (a : (Fin 3 → ℤ) → (Fin 4 → Mom d) → ℂ),
      (∀ m, 0 ≤ w m) ∧ (∀ m E, ‖a m E‖ ≤ 1) ∧
      (∀ t ∈ outBox (Dj j c), ∀ E ∈ Kj j c, HasSum (fun m => (w m : ℂ) * a m E * fsPhase m t)
        (f j t (sumintBoundary (σ j) E))) ∧ Summable w ∧ ∑' m, w m ≤ C * M j := fun j c =>
    hsup (Dj j c) (Kj j c) (fun t E => f j t (sumintBoundary (σ j) E)) (M j) (hM j) (hcont j c) (hbd j c)
  choose w a hw0 ha hser hws hwb using hex
  refine ⟨{ Λ := fun _ _ => Fin 3 → ℤ
            cnt := fun _ _ => inferInstance
            w := w
            m := fun _ _ m => m
            a := fun j c m k => a j c m (sumintBoundary (σ j) k)
            w_nn := hw0
            w_sum := hws
            a_one := fun j c m k => ha j c m _ }, hwb, ?_⟩
  intro j c t ht k hk
  have h := hser j c t ht (sumintBoundary (σ j) k) hk
  rwa [sumintBoundary_invol] at h

/-- The output momentum set of a `sumint` datum, unfolded: lattice coset, unit balls around the centre, the
conservation `v₀ - v₁ = v₃ - v₂` and the small gap `0 < ‖v₀ - v₁‖ ≤ L^{-γ+η}`. -/
theorem mem_outSet_iff {d : ℕ} (D : SumintDatum d) (L γ η : ℝ) (v : Fin 4 → Mom d) :
    v ∈ outSet D L γ η ↔ (∀ c, (∃ nv : Fin d → ℤ, v c = D.wBar + latticePoint L nv) ∧ ‖v c - D.centre c‖ ≤ 1) ∧
      v 0 - v 1 = v 3 - v 2 ∧ v 0 ≠ v 1 ∧ ‖v 0 - v 1‖ ≤ L ^ (-γ + η) := Iff.rfl

end WaveTurbulence.Represents
