/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtTa.Op
public import WaveTurbulence.Foundations.Fourier.Norm00VProduct

/-! # PROT-TA: o73 Lemma 12.2 (tensor version), norm form

Lemma 12.2 applies (12.1) to a product `H = H₁H₂H₃H₄` of four kernels, each with a finite `𝔛^{θ,0,0}` norm of its
extension to `ℝ³`, and the product bound comes from the algebra property of `A^θ` (`k`-supremum inside:
`mixedFourierNorm00_mul_le`): the output norm is at most `C_θ (2^θ)³ ∏ ‖H_i‖`, uniformly in `A`. The coefficient-level
statement (12.4) (extracted/integrable spectral sets, `(2|ρ|)!` derivative bounds) is not formalized here; this is the
norm-level consequence used by the consumers. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtTa

theorem XNorm_eq_mixed {r d : ℕ} (θ : ℝ) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNorm θ 0 0 F = mixedFourierNorm00 θ F := by
  rw [NormBridgeScratch.XNorm_zero_eq_XNorm00, NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]

theorem XNorm_mul4_le {d : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) (H : Fin 4 → (Fin 3 → ℝ) → Mom d → ℂ)
    (hc : ∀ i k, Continuous fun t => H i t k) (hf : ∀ i, XNorm θ 0 0 (H i) < ⊤) :
    XNorm θ 0 0 (fun t k => ∏ i, H i t k) ≤
      ENNReal.ofReal (2 ^ θ) ^ 3 * ∏ i, XNorm θ 0 0 (H i) := by
  simp only [XNorm_eq_mixed] at hf ⊢
  simp only [Fin.prod_univ_four]
  have h01 := mixedFourierNorm00_mul_le hθ0 (F := H 0) (G := H 1) (fun k => hc 1 k) (hf 0) (hf 1)
  have h01t : mixedFourierNorm00 θ (fun t k => H 0 t k * H 1 t k) < ⊤ :=
    h01.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hf 0)) (hf 1))
  have h012 := mixedFourierNorm00_mul_le hθ0 (F := fun t k => H 0 t k * H 1 t k) (G := H 2)
    (fun k => hc 2 k) h01t (hf 2)
  have h012t : mixedFourierNorm00 θ (fun t k => H 0 t k * H 1 t k * H 2 t k) < ⊤ :=
    h012.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h01t) (hf 2))
  have h0123 := mixedFourierNorm00_mul_le hθ0 (F := fun t k => H 0 t k * H 1 t k * H 2 t k)
    (G := H 3) (fun k => hc 3 k) h012t (hf 3)
  calc mixedFourierNorm00 θ (fun t k => H 0 t k * H 1 t k * H 2 t k * H 3 t k)
      ≤ ENNReal.ofReal (2 ^ θ) * mixedFourierNorm00 θ (fun t k => H 0 t k * H 1 t k * H 2 t k) *
          mixedFourierNorm00 θ (H 3) := h0123
    _ ≤ ENNReal.ofReal (2 ^ θ) * (ENNReal.ofReal (2 ^ θ) *
          (ENNReal.ofReal (2 ^ θ) * mixedFourierNorm00 θ (H 0) * mixedFourierNorm00 θ (H 1)) *
          mixedFourierNorm00 θ (H 2)) * mixedFourierNorm00 θ (H 3) := by
        gcongr
        refine h012.trans ?_
        gcongr
    _ = _ := by ring

/-- **o73 Lemma 12.2** (norm form): the consumed-modulation operator applied to a product of four kernels. -/
theorem terminalOperator_mul4 (d : ℕ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ) (H : Fin 4 → (Fin 3 → ℝ) → Mom d → ℂ) (K : Set (Mom d)),
      (∀ i k, Continuous fun t => H i t k) → (∀ i, XNorm θ 0 0 (H i) < ⊤) →
      XNormRestr θ 0 0 {ts : Fin 2 → ℝ | 0 < ts 1 ∧ ts 1 < ts 0 ∧ ts 0 < 1} K
        (fun ts k => ∫ u in ts 1..ts 0,
          Complex.exp (((Real.pi * A * (u - ts 1) : ℝ) : ℂ) * Complex.I) * ∏ i, H i ![ts 0, u, ts 1] k) ≤
      ENNReal.ofReal C * ∏ i, XNorm θ 0 0 (H i) := by
  obtain ⟨C, hC, h⟩ := terminalOperatorBound d θ hθ0 hθ1
  refine ⟨C * (2 ^ θ) ^ 3, by positivity, fun A H K hc hf => ?_⟩
  refine (h A (fun t k => ∏ i, H i t k) K).trans ?_
  calc ENNReal.ofReal C * XNorm θ 0 0 (fun t k => ∏ i, H i t k)
      ≤ ENNReal.ofReal C * (ENNReal.ofReal (2 ^ θ) ^ 3 * ∏ i, XNorm θ 0 0 (H i)) :=
        mul_le_mul_right (XNorm_mul4_le hθ0 H hc hf) _
    _ = ENNReal.ofReal (C * (2 ^ θ) ^ 3) * ∏ i, XNorm θ 0 0 (H i) := by
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_pow (by positivity)]
        ring

end WaveTurbulence.Flower.ProtTa
