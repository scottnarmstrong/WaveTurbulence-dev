/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.QuadraticStrip
import Mathlib.Tactic

/-!
# Counting short Cartesian cells

Finite covering machinery for the elementary annulus estimate in DH23
`basiccount0pre` (1): a projection contained in an interval of length `2L`
meets at most `2L/T+2` floor cells of width `T`.
-/

public section

namespace WaveTurbulence.Counting

/-- Points in the same floor cell have distance at most the cell width. -/
theorem abs_sub_le_of_floor_div_eq {x y T : ℝ} (hT : 0 < T)
    (he : ⌊x/T⌋ = ⌊y/T⌋) : |x-y| ≤ T := by
  have hx := (le_div_iff₀ hT).mp (Int.floor_le (x/T))
  have hx' := (div_lt_iff₀ hT).mp (Int.lt_floor_add_one (x/T))
  have hy := (le_div_iff₀ hT).mp (Int.floor_le (y/T))
  have hy' := (div_lt_iff₀ hT).mp (Int.lt_floor_add_one (y/T))
  rw [← he] at hy hy'
  apply abs_le.mpr
  constructor <;> nlinarith only [hx,hx',hy,hy']

/-- Explicit count of the cells intersecting a finite set whose projection
lies in a real interval of radius `L`. -/
theorem card_floor_cells_le {α : Type*} (s : Finset α) (f : α → ℝ)
    {d L T : ℝ} (hL : 0 ≤ L) (hT : 0 < T)
    (hproj : ∀ x ∈ s, |f x-d| ≤ L) :
    ((s.image (fun x => ⌊f x/T⌋)).card:ℝ) ≤ 2*L/T+2 := by
  classical
  have hb (k : ℤ) (hk : k ∈ s.image (fun x => ⌊f x/T⌋)) :
      (d-L)/T-1 ≤ (k:ℝ) ∧ (k:ℝ) ≤ (d+L)/T := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hk
    have hp := abs_le.mp (hproj x hx)
    have hlo : (d-L)/T ≤ f x/T := div_le_div_of_nonneg_right (by linarith only [hp.1]) hT.le
    have hhi : f x/T ≤ (d+L)/T := div_le_div_of_nonneg_right (by linarith only [hp.2]) hT.le
    have hflo := Int.lt_floor_add_one (f x/T)
    have hfhi := Int.floor_le (f x/T)
    constructor <;> linarith only [hlo,hhi,hflo,hfhi]
  have hc := card_int_finset_le_of_diameter (s.image (fun x => ⌊f x/T⌋))
    (D := 2*L/T+1) (by positivity) (by
      intro k hk l hl
      have hk' := hb k hk
      have hl' := hb l hl
      have he : (d+L)/T-((d-L)/T-1) = 2*L/T+1 := by ring
      rw [← he]
      apply abs_le.mpr
      constructor <;> linarith only [hk'.1,hk'.2,hl'.1,hl'.2])
  linarith only [hc]

end WaveTurbulence.Counting
