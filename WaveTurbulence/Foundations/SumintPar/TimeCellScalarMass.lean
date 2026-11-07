/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.TimeCellPartition
public import WaveTurbulence.Foundations.SumintPar.ScalarCellMass

/-!
# Ordinary smooth compact scalar time cells and their uniform Fourier mass

The scalar profile is exactly the landed partition theta1. Its Fourier
mass is finite and scales by at most h inverse, uniformly in every
integer cell center.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical ContDiff
namespace WaveTurbulence.SumintPar

/-- The actual scalar partition profile as a complex multiplier. -/
@[expose] noncomputable def timePartitionScalar (t : ℝ) : ℂ := ApproxNT.theta1 t

/-- The scalar source partition profile is ordinarily smooth. -/
theorem contDiff_timePartitionScalar : ContDiff ℝ ∞ timePartitionScalar :=
  Complex.ofRealCLM.contDiff.comp ApproxNT.contDiff_theta1

/-- The scalar source partition profile is compactly supported on [-1,1]. -/
theorem hasCompactSupport_timePartitionScalar : HasCompactSupport timePartitionScalar := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1:ℝ)) (b := 1))
  intro t ht
  have ha : 1 ≤ |t| := by
    by_contra! hn
    exact ht ⟨(abs_lt.mp hn).1.le,(abs_lt.mp hn).2.le⟩
  simp only [timePartitionScalar,ApproxNT.theta1_eq_zero ha,Complex.ofReal_zero]

/-- Each actual complex time-cell profile is ordinarily smooth. -/
theorem contDiff_complex_timeCellProfile (h : ℝ) (j : ℤ) :
    ContDiff ℝ ∞ (fun t => (timeCellProfile h j t:ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_timeCellProfile h j)

/-- Every positive-scale time-cell profile is genuinely compactly supported. -/
theorem hasCompactSupport_complex_timeCellProfile {h : ℝ} (hh : 0 < h) (j : ℤ) :
    HasCompactSupport (fun t => (timeCellProfile h j t:ℂ)) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (j:ℝ)*h-h) (b := (j:ℝ)*h+h))
  intro t ht
  have hz : timeCellProfile h j t = 0 := by
    by_contra hn
    have ha := abs_sub_cell_le_of_timeCellProfile_ne_zero hh j hn
    have hb := abs_le.mp ha
    apply ht
    constructor <;> linarith only [hb.1,hb.2]
  rw [hz,Complex.ofReal_zero]

/-- The actual scalar cell Fourier mass has the uniform h-inverse bound. -/
theorem scalarFourierMass_timeCellProfile_le {h : ℝ} (hh : h ∈ Ioc (0:ℝ) 1) (j : ℤ) :
    scalarFourierMass (fun t => (timeCellProfile h j t:ℂ)) ≤
      ENNReal.ofReal h⁻¹*scalarFourierMass timePartitionScalar := by
  have he : (fun t => timePartitionScalar ((t-(j:ℝ)*h)/h)) = fun t => (timeCellProfile h j t:ℂ) := by
    funext t
    unfold timePartitionScalar timeCellProfile
    congr 2
    field_simp [hh.1.ne']
  rw [← he]
  exact scalarFourierMass_cell_le hh timePartitionScalar ((j:ℝ)*h)

end WaveTurbulence.SumintPar
