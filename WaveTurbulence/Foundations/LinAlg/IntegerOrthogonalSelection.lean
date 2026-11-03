/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LinAlg.IntegerGramResidual
public import WaveTurbulence.Foundations.LinAlg.MaxVolume

/-!
# Bounded orthogonal selection on the integer lattice

The quantitative integer Gram–Schmidt step in TARGET Lemma A.6. A bounded
finite integer family has an orthogonal integer spanning family with bounds
`(d+1)! B^(2d+1)`, also for a linear functional bounded on the input family.
-/

public section

namespace WaveTurbulence.LinAlg
open Finset Module
open scoped Classical InnerProductSpace

/-- A finite bounded integer set admits a polynomially bounded orthogonal
integer spanning family. The empty span is represented by the empty family. -/
theorem exists_integer_orthogonal_selection {d : ℕ} (H : Finset (Fin d → ℤ))
    {B : ℝ} (hB : 1 ≤ B) (hH : ∀ w ∈ H, ‖latticePoint 1 w‖ ≤ B)
    (ℓ : Mom d →ₗ[ℝ] ℝ) (hℓ : ∀ w ∈ H, |ℓ (latticePoint 1 w)| ≤ B) :
    ∃ q ≤ d, ∃ v : Fin q → Fin d → ℤ,
      (∀ i, latticePoint 1 (v i) ≠ 0) ∧
      (Pairwise fun i j => ⟪latticePoint 1 (v i), latticePoint 1 (v j)⟫_ℝ = 0) ∧
      Submodule.span ℝ (Set.range fun i => latticePoint 1 (v i)) =
        Submodule.span ℝ ((H.image (latticePoint 1) : Finset (Mom d)) : Set (Mom d)) ∧
      (∀ i, ‖latticePoint 1 (v i)‖ ≤ (d + 1).factorial * B ^ (2 * d + 1)) ∧
      (∀ i, |ℓ (latticePoint 1 (v i))| ≤ (d + 1).factorial * B ^ (2 * d + 1)) := by
  let S : Finset (Mom d) := H.image (latticePoint 1)
  let W := Submodule.span ℝ (S : Set (Mom d))
  obtain ⟨f, hf, hspan, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ (S : Set (Mom d))
  have hq : finrank ℝ W ≤ d := by simpa [Mom] using W.finrank_le
  have hex (i : Fin (finrank ℝ W)) : ∃ w ∈ H, latticePoint 1 w = f i :=
    mem_image.mp (hf i)
  choose w hwH hwf using hex
  have hfcast : (fun i => latticePoint 1 (w i)) = f := funext hwf
  let v := integerOrthogonalFamily w
  have hv (i) : latticePoint 1 (v i) = orthogonalResidualFamily f i := by
    rw [← hfcast]
    exact (integerOrthogonalFamily_cast w i).symm
  have hbound : ((finrank ℝ W + 1).factorial : ℝ) * B ^ (2 * finrank ℝ W + 1) ≤
      (d + 1).factorial * B ^ (2 * d + 1) := by
    apply mul_le_mul
    · exact_mod_cast Nat.factorial_le (Nat.add_le_add_right hq 1)
    · exact pow_le_pow_right₀ hB (by omega)
    · positivity
    · positivity
  refine ⟨finrank ℝ W, hq, v, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hv]
    exact orthogonalResidualFamily_ne_zero hli i
  · intro i j hij
    rw [hv, hv]
    exact orthogonalResidualFamily_pairwise f hij
  · simp_rw [hv]
    exact (span_orthogonalResidualFamily hli).trans hspan
  · intro i
    rw [hv, ← hfcast]
    exact (norm_orthogonalResidualFamily_le hB (fun j => hH _ (hwH j)) i).trans hbound
  · intro i
    rw [hv, ← hfcast]
    exact (abs_apply_orthogonalResidualFamily_le hB (fun j => hH _ (hwH j)) ℓ
      (fun j => hℓ _ (hwH j)) i).trans hbound

end WaveTurbulence.LinAlg
