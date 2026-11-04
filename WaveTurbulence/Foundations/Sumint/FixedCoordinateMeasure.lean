/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Product measures with selected input times fixed

A fixed coordinate carries a Dirac measure and every other coordinate
carries Lebesgue measure. Both are sigma finite. Each enlarged source
interval has mass at most three in either case, so an affected core of
arity a costs at most 3 to the power a in time volume.
-/

public section

open MeasureTheory Set ENNReal
open scoped Classical

namespace WaveTurbulence.Sumint

/-- Coordinate measure fixing selected times and integrating all other times against Lebesgue measure. -/
@[expose] noncomputable def fixedCoordinateMeasure {ι : Type*} (s : Set ι) (x : ι → ℝ) (i : ι) : Measure ℝ :=
  if i ∈ s then Measure.dirac (x i) else volume

instance {ι : Type*} (s : Set ι) (x : ι → ℝ) (i : ι) : SigmaFinite (fixedCoordinateMeasure s x i) := by
  unfold fixedCoordinateMeasure
  split_ifs <;> infer_instance

/-- Every source interval of length at most three has mass at most three, fixed or free. -/
theorem fixedCoordinateMeasure_Icc_le_three {ι : Type*} (s : Set ι) (x : ι → ℝ) (i : ι)
    (a b : ℝ) (hlen : b-a ≤ 3) : fixedCoordinateMeasure s x i (Icc a b) ≤ ENNReal.ofReal 3 := by
  unfold fixedCoordinateMeasure
  split_ifs
  · rcases (Measure.dirac_apply_eq_zero_or_one (a := x i) (s := Icc a b)) with h | h <;> rw [h] <;> norm_num
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal hlen

/-- A finite coordinate box has at most three to its arity units of fixed/free product mass. -/
theorem fixedCoordinateMeasure_pi_box_le {ι κ : Type*} [Fintype κ]
    (s : Set ι) (x : ι → ℝ) (v : κ → ι) (lo hi : κ → ℝ) (hlen : ∀ j, hi j-lo j ≤ 3) :
    (Measure.pi (fun j => fixedCoordinateMeasure s x (v j)))
      (Set.pi Set.univ (fun j => Icc (lo j) (hi j))) ≤ ENNReal.ofReal (3^(Fintype.card κ):ℝ) := by
  rw [Measure.pi_pi]
  calc
    _ ≤ ∏ _j : κ, ENNReal.ofReal 3 := Finset.prod_le_prod
      (fun j _ => fixedCoordinateMeasure_Icc_le_three s x (v j) (lo j) (hi j) (hlen j))
    _ = _ := by rw [Finset.prod_const,Finset.card_univ,ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 3)]

end WaveTurbulence.Sumint
