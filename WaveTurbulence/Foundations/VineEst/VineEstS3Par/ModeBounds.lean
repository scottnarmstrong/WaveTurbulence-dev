/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ClockPhase
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Brackets
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ScaledSumint

/-! # The cost of a mode: parameters and output frequencies (engine step ASM)

For a mode tuple `m`, `⟨Δ_m(v)⟩ ≲ (√2)^{2|ρ|} ∏_ρ (2 ⟨m_ρ/2⟩)^2`, and likewise for the output frequency.  Hence the
`η⁶`-power of the maximal parameter of the shifted datum and the output modulation cost
are bounded by `C^{|ρ|} maxPar(D)^{η⁶} ∏_ρ ⟨m_ρ/2⟩^{θ}`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS Finset
open scoped ENNReal

variable {d : ℕ} (D : SumintPar.SumintDatum d)


theorem jbr_one_dim (t : ℝ) : jbr (d := 1) (WithLp.toLp 2 fun _ => t) = WaveTurbulence.VineEstS3.Eng.Jb t := by
  unfold jbr WaveTurbulence.VineEstS3.Eng.Jb
  congr 2
  rw [EuclideanSpace.norm_eq]
  simp [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Real.sqrt_sq_eq_abs, sq_abs]

theorem maxPar_eq (D' : SumintPar.SumintDatum d) : maxPar D' = ⨆ v, WaveTurbulence.VineEstS3.Eng.Jb (D'.param v) := by
  unfold maxPar
  exact iSup_congr fun v => jbr_one_dim _

theorem one_le_prod_real {ι : Type*} [Fintype ι] (f : ι → ℝ) (h : ∀ i, 1 ≤ f i) : 1 ≤ ∏ i, f i := by
  calc (1 : ℝ) = ∏ _i : ι, (1 : ℝ) := by simp
    _ ≤ ∏ i, f i := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun i _ => h i)

end WaveTurbulence.VineEstS3Par.Eng
