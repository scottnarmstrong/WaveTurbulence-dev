/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.TimeCellNorm
public import WaveTurbulence.Foundations.SumintPar.SourceShearNorm
public import WaveTurbulence.Foundations.SumintPar.ParameterModulation

/-!
# The explicit ambient extension of each weighted localized source integral

Finite time-cell recombination is followed by the actual source time
shear and the parameter modulation. Agreement is pointwise on the full
source cube; the norm bound retains all output variables inside its supremum.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
namespace WaveTurbulence.SumintPar

/-- The actual ambient extension in original source output coordinates. -/
@[expose] noncomputable def weightedSourceExtension {d : ℕ} (D : SumintDatum d)
    (hI : 0 < D.S.I) (N : ℕ) (h L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d)
    (t : Fin 3 → ℝ) : ℂ :=
  Complex.exp ((Real.pi*(∑ v, D.param v)*t 0 : ℝ)*Complex.I) *
    timeCellExtension D hI N h (weightedCutoffInput D L γ δ η p ν r) (sourceTimeShear t)

/-- The complete explicit extension obeys the cell, shear and modulation costs. -/
theorem XNorm00_weightedSourceExtension_le {d : ℕ} {V : Type*} (D : SumintDatum d)
    (hI : 0 < D.S.I) (N : ℕ) {h θ : ℝ} (hh : h ∈ Ioc (0:ℝ) 1)
    (hθ : θ ∈ Icc (0:ℝ) 1) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : V → Mom d)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (hF : ∀ j : ℤ, XNorm00 θ (fun z v => kernelExtension D hI ((j:ℝ)*h) h
      (weightedCutoffInput D L γ δ η p ν (r v)) z) ≤ B) :
    XNorm00 θ (fun t v => weightedSourceExtension D hI N h L γ δ η p ν (r v) t) ≤
      ENNReal.ofReal (2^θ)*
        ENNReal.ofReal ((((D.S.M:ℝ)+1)*parameterMaximum D)^θ)*
        (ENNReal.ofReal (4^θ)*
          (ENNReal.ofReal (cellMultiplierRealConstant N*((N:ℝ)+5)*h⁻¹*h⁻¹)*B)) := by
  have hc := XNorm00_timeCellExtension_le D hI N hh
    (by simpa only [abs_of_nonneg hθ.1] using hθ.2)
    (fun v => weightedCutoffInput D L γ δ η p ν (r v)) B hB hF
  have hs := (XNorm00_sourceTimeShear_le hθ.1
    (fun z v => timeCellExtension D hI N h (weightedCutoffInput D L γ δ η p ν (r v)) z)).trans
      (mul_le_mul' le_rfl hc)
  exact (XNorm00_source_modulate_le D hI θ _).trans (by
    simpa only [abs_of_nonneg hθ.1] using mul_le_mul' le_rfl hs)

end WaveTurbulence.SumintPar
