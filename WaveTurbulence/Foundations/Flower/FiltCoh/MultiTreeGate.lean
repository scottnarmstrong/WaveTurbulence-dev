/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.MultiTree
public import WaveTurbulence.Foundations.Spine.PL2330Draft.TreeGate

/-! # FILT-COH: coherent paired trees `(q, q')`, any weight `θ ∈ [0, 1]` (bound only)

The case split of main's `PL2330.tree_err_gt30` (single block / top block in layer `q` / root below `q`) and
`tree_same30`, for the kernel alone. The constant is `G' = 2 K_tr(θ) cLeib C²`. -/

public section
open WaveTurbulence.Induct
open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltCoh

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.PL2330 WaveTurbulence.Reg WaveTurbulence.Links

variable {d : ℕ}

/-- The constant of the coherent tree bound. -/
@[expose] noncomputable def treeG (d : ℕ) (θ C : ℝ) : ℝ := 2 * (Ktr θ * cLeib d (30 * d) * C ^ 2)

theorem le_treeG {d : ℕ} (hd : 1 ≤ d) {θ C : ℝ} (hθ : 0 ≤ θ) (hC : 1 ≤ C) :
    C ≤ treeG d θ C ∧ Ktr θ * cLeib d (30 * d) * C ^ 2 ≤ treeG d θ C ∧ 1 ≤ treeG d θ C := by
  have hK1 : 1 ≤ Ktr θ := one_le_Ktr hθ
  have hLc : 1 ≤ cLeib d (30 * d) := one_le_cLeib hd _
  have h1 : C ≤ Ktr θ * cLeib d (30 * d) * C ^ 2 := by
    have := mul_le_mul (mul_le_mul hK1 hLc zero_le_one (by linarith)) (pow_le_pow_right₀ hC
      (by norm_num : 1 ≤ 2)) (by positivity) (by positivity)
    simpa using this
  have h0 : 0 ≤ Ktr θ * cLeib d (30 * d) * C ^ 2 := by linarith
  unfold treeG
  refine ⟨by linarith, by linarith, by linarith⟩

theorem bound_mono_G {C G δ β : ℝ} (n : ℕ) (hC : 0 ≤ C) (hCG : C ≤ G) (hδ : 0 ≤ δ) (hβ : 0 ≤ β) :
    C * (C * δ) ^ n * β ≤ G * (G * δ) ^ n * β :=
  mul_le_mul_of_nonneg_right (mul_le_mul hCG (pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_right hCG hδ) n) (by positivity) (hC.trans hCG)) hβ


theorem ofReal_mul4 {a b c e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c * ENNReal.ofReal e =
      ENNReal.ofReal (a * b * c * e) := by
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul (mul_nonneg ha hb),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg ha hb) hc)]

section Gate

variable {L γ δ θ : ℝ} {Nmax : ℕ} {C : ℝ} (O : TreeKOracle d L γ δ θ Nmax C) (hC : 1 ≤ C)
  (hd : 1 ≤ d) (hL : 1 ≤ L) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hδ : 0 ≤ δ)

include O hC hd hL hθ0 hθ1 hδ

end Gate

end WaveTurbulence.Flower.FiltCoh
