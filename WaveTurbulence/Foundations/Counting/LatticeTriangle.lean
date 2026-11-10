/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Integer determinants and thin planar sections

DH23 `basiccount0pre` (1), elementary branch (TeX L2040–L2043): a sufficiently
small annulus section cannot contain three noncollinear integer points. The
arithmetic ingredient is integrality of the determinant of two lattice
increments. This module supplies that ingredient and an explicit thin-box
criterion, including boxes expressed in an area-preserving real frame.
-/

public section

namespace WaveTurbulence.Counting

/-- Signed determinant of two integer planar vectors. -/
@[expose] def latticeDet (u v : Fin 2 → ℤ) : ℤ := u 0*v 1-u 1*v 0

/-- The signed doubled area of a lattice triangle is an integer. -/
@[expose] def latticeTriangleDet (p q r : Fin 2 → ℤ) : ℤ :=
  latticeDet (q-p) (r-p)

/-- An integer determinant with absolute value below one vanishes. -/
theorem latticeTriangleDet_eq_zero_of_abs_lt_one {p q r : Fin 2 → ℤ}
    (h : |(latticeTriangleDet p q r:ℝ)| < 1) : latticeTriangleDet p q r = 0 := by
  rw [← Int.cast_abs] at h
  have hi : |latticeTriangleDet p q r| < (1:ℤ) := by exact_mod_cast h
  have ha := le_abs_self (latticeTriangleDet p q r)
  have hb := neg_abs_le (latticeTriangleDet p q r)
  omega

/-- Determinant under a real linear change of planar coordinates. -/
theorem planar_det_change_frame (a b c d x₁ x₂ y₁ y₂ : ℝ) :
    (a*x₁+b*x₂)*(c*y₁+d*y₂) - (c*x₁+d*x₂)*(a*y₁+b*y₂) =
      (a*d-b*c)*(x₁*y₂-x₂*y₁) := by ring

/-- Two planar increments in a box of coordinate bounds `W,T` have determinant
at most `2*W*T` in absolute value. -/
theorem abs_planar_det_le {x₁ x₂ y₁ y₂ W T : ℝ}
    (hx₁ : |x₁| ≤ W) (hy₁ : |y₁| ≤ W)
    (hx₂ : |x₂| ≤ T) (hy₂ : |y₂| ≤ T) :
    |x₁*y₂-x₂*y₁| ≤ 2*W*T := by
  have hW : 0 ≤ W := (abs_nonneg _).trans hx₁
  have hT : 0 ≤ T := (abs_nonneg _).trans hx₂
  calc
    _ ≤ |x₁*y₂|+|x₂*y₁| := by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (x₁*y₂) 0 (x₂*y₁)
    _ = |x₁| *|y₂|+|x₂| *|y₁| := by rw [abs_mul,abs_mul]
    _ ≤ W*T+T*W := add_le_add
      (mul_le_mul hx₁ hy₂ (abs_nonneg _) hW)
      (mul_le_mul hx₂ hy₁ (abs_nonneg _) hT)
    _ = _ := by ring

/-- A thin box in an area-preserving frame cannot support a nondegenerate
lattice triangle. The hypotheses bound the actual two lattice increments. -/
theorem latticeTriangleDet_eq_zero_of_thin_frame {p q r : Fin 2 → ℤ}
    {a b c d W T : ℝ} (hframe : a*d-b*c = 1)
    (hq₁ : |a*((q 0-p 0:ℤ):ℝ)+b*((q 1-p 1:ℤ):ℝ)| ≤ W)
    (hr₁ : |a*((r 0-p 0:ℤ):ℝ)+b*((r 1-p 1:ℤ):ℝ)| ≤ W)
    (hq₂ : |c*((q 0-p 0:ℤ):ℝ)+d*((q 1-p 1:ℤ):ℝ)| ≤ T)
    (hr₂ : |c*((r 0-p 0:ℤ):ℝ)+d*((r 1-p 1:ℤ):ℝ)| ≤ T)
    (hsmall : 2*W*T < 1) : latticeTriangleDet p q r = 0 := by
  apply latticeTriangleDet_eq_zero_of_abs_lt_one
  have hb := abs_planar_det_le hq₁ hr₁ hq₂ hr₂
  rw [planar_det_change_frame, hframe, one_mul] at hb
  have he : (latticeTriangleDet p q r:ℝ) =
      ((q 0-p 0:ℤ):ℝ)*((r 1-p 1:ℤ):ℝ)-((q 1-p 1:ℤ):ℝ)*((r 0-p 0:ℤ):ℝ) := by
    simp only [latticeTriangleDet,latticeDet,Pi.sub_apply,Int.cast_sub,Int.cast_mul]
  rw [he]
  exact hb.trans_lt hsmall

/-- A nonvertical degenerate lattice triangle lies on the affine graph through
its first two vertices. -/
theorem exists_affine_graph_of_triangleDet_eq_zero (s : Finset (Fin 2 → ℤ))
    (p q : Fin 2 → ℤ) (hn : q 0-p 0 ≠ 0)
    (hdet : ∀ r ∈ s, latticeTriangleDet p q r = 0) :
    ∃ m b : ℝ, ∀ r ∈ s, (r 1:ℝ) = m*(r 0:ℝ)+b := by
  let m : ℝ := ((q 1:ℝ)-p 1)/((q 0:ℝ)-p 0)
  refine ⟨m,(p 1:ℝ)-m*(p 0:ℝ),?_⟩
  intro r hr
  have hd := hdet r hr
  simp only [latticeTriangleDet,latticeDet,Pi.sub_apply] at hd
  have hdR : ((q 0:ℝ)-p 0)*((r 1:ℝ)-p 1)-
      ((q 1:ℝ)-p 1)*((r 0:ℝ)-p 0) = 0 := by exact_mod_cast hd
  have hnR : (q 0:ℝ)-(p 0:ℝ) ≠ 0 := by exact_mod_cast hn
  dsimp only [m]
  field_simp [hnR]
  nlinarith only [hdR]

end WaveTurbulence.Counting
