/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.LocalizedWeight
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

/-!
# Unit-volume support boxes for localized sumint weights

Each half-mesh partition piece is supported in a closed cube of side
length one. Its Euclidean-space Lebesgue volume is exactly one, uniformly
in the center and also in dimension zero.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set

namespace WaveTurbulence.SumintPar

/-- The closed unit-side coordinate cube centered at `a/2`. -/
@[expose] noncomputable def localizationBox {d : ℕ} (a : Fin d → ℤ) : Set (Mom d) :=
  WithLp.ofLp ⁻¹' Icc (fun i => (a i : ℝ) / 2 - 1 / 2) (fun i => (a i : ℝ) / 2 + 1 / 2)

/-- The support box is closed. -/
theorem localizationBox_isClosed {d : ℕ} (a : Fin d → ℤ) : IsClosed (localizationBox a) := by
  exact isClosed_Icc.preimage (show Continuous (WithLp.ofLp : Mom d → Fin d → ℝ) by fun_prop)

/-- Every nonzero partition piece lies in its unit-side cube. -/
theorem localizationProfile_mem_box {d : ℕ} {a : Fin d → ℤ} {x : Mom d}
    (hx : localizationProfile a x ≠ 0) : x ∈ localizationBox a := by
  have hb (i : Fin d) : |2 * x i - (a i : ℝ)| < 1 :=
    ApproxNT.abs_lt_one_of_thetaMom_ne_zero hx i
  constructor
  · intro i
    have hi := (abs_lt.mp (hb i)).1
    dsimp
    linarith
  · intro i
    have hi := (abs_lt.mp (hb i)).2
    dsimp
    linarith

/-- Topological support obeys the same closed cube bound. -/
theorem tsupport_localizationProfile_subset {d : ℕ} (a : Fin d → ℤ) :
    tsupport (localizationProfile a) ⊆ localizationBox a := by
  change closure (Function.support (localizationProfile a)) ⊆ localizationBox a
  exact closure_minimal (fun _ hx => localizationProfile_mem_box hx) (localizationBox_isClosed a)

/-- The localized weight and all its derivatives have support in the same cube. -/
theorem tsupport_localizedWeight_subset {d : ℕ} (a : Fin d → ℤ) (F : Mom d → ℂ) :
    tsupport (localizedWeight a F) ⊆ localizationBox a :=
  (tsupport_smul_subset_left (localizationProfile a) F).trans (tsupport_localizationProfile_subset a)

/-- No volume loss is paid for a localization center. -/
theorem volume_localizationBox {d : ℕ} (a : Fin d → ℤ) : volume (localizationBox a) = 1 := by
  rw [localizationBox, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage measurableSet_Icc.nullMeasurableSet,
    Real.volume_Icc_pi]
  have hi (i : Fin d) : (a i : ℝ) / 2 + 1 / 2 - ((a i : ℝ) / 2 - 1 / 2) = 1 := by ring
  simp only [hi, ENNReal.ofReal_one, Finset.prod_const_one]

end WaveTurbulence.SumintPar
