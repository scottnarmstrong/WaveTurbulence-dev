/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Fourier.PoissonBlocks
public import WaveTurbulence.Foundations.NTSP.Basic
public import WaveTurbulence.Frozen.Defs.LatticePoint

/-!
# Poisson summation for a pair of momentum variables (packet NT6)

For a smooth compactly supported `F` on `ℝ^d × ℝ^d`,
`∑_{(g,h) ∈ ℤ^{2d}} F(g/L, h/L) = L^{2d} ∑_{(g,h)} ∫∫ F(x,y) e(-L(g·x + h·y)) dx dy`.
This is the landed block Poisson formula (`Fourier.poisson_scaled_blocks`, two blocks),
transported to `Mom d × Mom d`.
-/

public section

noncomputable section

open MeasureTheory WithLp
open scoped SchwartzMap ContDiff

namespace WaveTurbulence.ApproxNT

variable {d : ℕ}

/-- The two-block coordinates of a pair of momenta. -/
@[expose] def pairCLE (d : ℕ) : (Fin 2 → Fin d → ℝ) ≃L[ℝ] Mom d × Mom d :=
  (ContinuousLinearEquiv.piFinTwo ℝ (fun _ => Fin d → ℝ)).trans
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.prodCongr
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm)

theorem pairCLE_apply (z : Fin 2 → Fin d → ℝ) :
    pairCLE d z = (toLp 2 (z 0), toLp 2 (z 1)) := rfl

theorem measurePreserving_pairCLE : MeasurePreserving (pairCLE d) := by
  have h1 := measurePreserving_finTwoArrow (volume : Measure (Fin d → ℝ))
  have h2 := (PiLp.volume_preserving_toLp (Fin d)).prod (PiLp.volume_preserving_toLp (Fin d))
  have h := h2.comp h1
  refine ⟨(pairCLE d).continuous.measurable, ?_⟩
  have he : (pairCLE d : (Fin 2 → Fin d → ℝ) → Mom d × Mom d) =
      (Prod.map (toLp 2) (toLp 2)) ∘ (MeasurableEquiv.finTwoArrow) := by
    funext z; rfl
  rw [he]
  exact h.map_eq

theorem timePairing_intVec (L : ℝ) (u : Fin d → ℝ) (g : Fin d → ℤ) :
    Fourier.timePairing d u (fun j => L * (g j : ℝ)) = L * inner ℝ (toLp 2 u) (NTSP.intVec g) := by
  simp only [Fourier.timePairing, dotProductBilin_apply_apply, dotProduct, PiLp.inner_apply,
    NTSP.intVec, RCLike.inner_apply, conj_trivial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Poisson summation on the pair lattice `(L⁻¹ℤ^d)²`. -/
theorem poisson_pair {F : Mom d → Mom d → ℂ}
    (hF : ContDiff ℝ ∞ (fun z : Mom d × Mom d => F z.1 z.2))
    (hFc : HasCompactSupport (fun z : Mom d × Mom d => F z.1 z.2)) {L : ℝ} (hL : 0 < L) :
    (∑' gh : (Fin d → ℤ) × (Fin d → ℤ), F (latticePoint L gh.1) (latticePoint L gh.2)) =
      (L ^ (2 * d) : ℂ) * ∑' gh : (Fin d → ℤ) × (Fin d → ℤ),
        ∫ z : Mom d × Mom d, Real.fourierChar
          (-(L * inner ℝ z.1 (NTSP.intVec gh.1) + L * inner ℝ z.2 (NTSP.intVec gh.2))) •
            F z.1 z.2 := by
  set G : Mom d × Mom d → ℂ := fun z => F z.1 z.2
  set f₀ : (Fin 2 → Fin d → ℝ) → ℂ := G ∘ pairCLE d
  have hf₀ : ContDiff ℝ ∞ f₀ := hF.comp (pairCLE d).contDiff
  have hf₀c : HasCompactSupport f₀ := hFc.comp_homeomorph (pairCLE d).toHomeomorph
  set f : 𝓢((Fin 2 → Fin d → ℝ), ℂ) := hf₀c.toSchwartzMap hf₀
  have hfe : ∀ z, f z = f₀ z := fun z => rfl
  have hP := Fourier.poisson_scaled_blocks f hL
  simp only [hfe] at hP
  -- left side
  have hl : (∑' a : Fin 2 → Fin d → ℤ, f₀ (fun i j => (a i j : ℝ) / L)) =
      ∑' gh : (Fin d → ℤ) × (Fin d → ℤ), F (latticePoint L gh.1) (latticePoint L gh.2) := by
    rw [← (finTwoArrowEquiv (Fin d → ℤ)).symm.tsum_eq]
    rfl
  -- right side
  have hr : ∀ b : Fin 2 → Fin d → ℤ, Fourier.blockFourier (⇑f) (fun i j => L * (b i j : ℝ)) =
      ∫ z : Mom d × Mom d, Real.fourierChar
          (-(L * inner ℝ z.1 (NTSP.intVec (b 0)) + L * inner ℝ z.2 (NTSP.intVec (b 1)))) •
            F z.1 z.2 := by
    intro b
    rw [Fourier.blockFourier, ← measurePreserving_pairCLE.integral_comp
      (pairCLE d).toHomeomorph.isClosedEmbedding.measurableEmbedding]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hfe, f₀, G, Function.comp_apply, pairCLE_apply, Fin.sum_univ_two,
      timePairing_intVec]
  rw [← hl, hP]
  congr 1
  rw [← (finTwoArrowEquiv (Fin d → ℤ)).symm.tsum_eq]
  exact tsum_congr fun gh => hr _

end WaveTurbulence.ApproxNT
