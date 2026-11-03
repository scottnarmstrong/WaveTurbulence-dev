/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LemLin.CubicTensor

/-!
# TARGET Lemma `lemcubic0`

The source's three integer vectors are grouped as `Fin d → Fin 3 → ℤ`,
with inner coordinates `0,1,2` corresponding to `g,h,q`. The integration
variables and all six translation/modulation vectors use the same grouping.
The result includes absolute summability, so its infinite sum is substantive.
-/

public section

namespace WaveTurbulence.LemLin
open Finset
open scoped Classical

/-- The three vector frequency lattices, grouped by spatial coordinate. -/
@[expose] def tensorLatticeFrequency {d : ℕ} (L : ℝ) (ξ : Fin d → Fin 3 → ℝ)
    (n : Fin d → Fin 3 → ℤ) : Fin d → Fin 3 → ℝ :=
  fun i => scalarLatticeFrequency L (ξ i) (n i)

/-- TARGET `lemcubic0`, L1544–L1553, for both choices of Λ and all centers and shifts. -/
theorem lemcubic0 (d : ℕ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ {L : ℝ}, 1 ≤ L → ∀ (kind : CubicPhase) (s t : ℝ), |s| ≤ L → |t| ≤ L →
      ∀ (a ξ : Fin d → Fin 3 → ℝ),
      Summable (fun n : Fin d → Fin 3 → ℤ =>
        ‖cubicTensorIntegral kind s t a (tensorLatticeFrequency L ξ n)‖) ∧
      (∑' n : Fin d → Fin 3 → ℤ,
        ‖cubicTensorIntegral kind s t a (tensorLatticeFrequency L ξ n)‖) ≤
          K / (1 + |s| + |t|) ^ d := by
  obtain ⟨C, hC, hscalar⟩ := scalarCubic_lattice_sum fixedCubicCutoffs
  refine ⟨C ^ d, pow_nonneg hC _, ?_⟩
  intro L hL kind s t hs ht a ξ
  let η : Fin d → Fin 3 → ℝ := fun i => ξ i + cubicFrequencyShift kind s t (a i)
  let F : Fin d → (Fin 3 → ℤ) → ℝ := fun i n =>
    ‖scalarCubicIntegral kind fixedCubicCutoffs s t (scalarLatticeFrequency L (η i) n)‖
  have hF0 (i : Fin d) (n : Fin 3 → ℤ) : 0 ≤ F i n := norm_nonneg _
  have hF (i : Fin d) : Summable (F i) := (hscalar hL kind s t hs ht (η i)).1
  have hFB (i : Fin d) : (∑' n, F i n) ≤ C / cubicScale s t :=
    (hscalar hL kind s t hs ht (η i)).2
  have hprod := summable_pi_product F hF0 hF (fun _ => C / cubicScale s t) hFB
  have he (n : Fin d → Fin 3 → ℤ) :
      ‖cubicTensorIntegral kind s t a (tensorLatticeFrequency L ξ n)‖ = ∏ i, F i (n i) := by
    rw [norm_cubicTensorIntegral_eq_prod]
    apply prod_congr rfl
    intro i _
    congr 2
    ext j
    dsimp [tensorLatticeFrequency, scalarLatticeFrequency, η]
    ring
  constructor
  · simpa only [he] using hprod.1
  · calc
      _ = ∑' n : Fin d → Fin 3 → ℤ, ∏ i, F i (n i) := tsum_congr he
      _ ≤ ∏ _i : Fin d, C / cubicScale s t := hprod.2
      _ = _ := by simp only [prod_const, card_univ, Fintype.card_fin, div_pow, cubicScale]

end WaveTurbulence.LemLin
