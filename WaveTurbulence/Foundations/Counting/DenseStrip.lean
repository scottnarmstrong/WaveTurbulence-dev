/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.IntervalCells
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Short integer relations from dense strips

DH23 `basiccount0pre` (2), `estcross`, TeX L2045–L2047: a dense planar strip
with a dominant first coefficient yields a short nontrivial integer relation.
This is the explicit floor-cell pigeonhole argument, with no Diophantine
approximation assumption.
-/

public section

namespace WaveTurbulence.Counting

/-- Density in a planar strip forces a short integer relation whose second
coordinate is nonzero. The constants implement the source's pigeonhole step. -/
theorem exists_small_relation_of_dense_strip (s : Finset (Fin 2 → ℤ))
    {a b alpha rho theta L d : ℝ}
    (hrho : 0 ≤ rho) (htheta : 1 ≤ theta) (hL : 16*theta ≤ L)
    (ha : 2*rho < |a|) (hb : |b| ≤ |a|)
    (hproj : ∀ n ∈ s, |(n 1:ℝ)-d| ≤ L)
    (hstrip : ∀ n ∈ s, |a*(n 0:ℝ)+b*(n 1:ℝ)-alpha| ≤ rho)
    (hdense : L/theta ≤ (s.card:ℝ)) :
    ∃ m n : ℤ, n ≠ 0 ∧ |(n:ℝ)| ≤ 8*theta ∧ |(m:ℝ)| ≤ 9*theta ∧
      |a*(m:ℝ)+b*(n:ℝ)| ≤ 2*rho := by
  classical
  have ht : 0 < theta := lt_of_lt_of_le zero_lt_one htheta
  have hLp : 0 ≤ L := by linarith only [hL,htheta]
  let f : (Fin 2 → ℤ) → ℤ := fun n => ⌊(n 1:ℝ)/(8*theta)⌋
  have hcells := card_floor_cells_le s (fun n : Fin 2 → ℤ => (n 1:ℝ)) hLp
    (by positivity : 0 < 8*theta) hproj
  have hid : 2*L/(8*theta)+2 = (L/theta)/4+2 := by field_simp; ring
  rw [hid] at hcells
  have hlarge : 16 ≤ L/theta := (le_div_iff₀ ht).mpr hL
  have hsmall : ((s.image f).card:ℝ) < (s.card:ℝ) := by
    linarith only [hcells,hdense,hlarge]
  have hcollision : ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ f p = f q := by
    by_contra h
    push Not at h
    have hinj : Set.InjOn f (s : Set (Fin 2 → ℤ)) := by
      intro p hp q hq he
      by_contra hne
      exact h p hp q hq hne he
    have hc := Finset.card_image_of_injOn hinj
    rw [hc] at hsmall
    exact (lt_irrefl _ hsmall)
  obtain ⟨p,hp,q,hq,hpq,hcell⟩ := hcollision
  let m : ℤ := q 0-p 0
  let n : ℤ := q 1-p 1
  have hnabs : |(n:ℝ)| ≤ 8*theta := by
    change |((q 1-p 1:ℤ):ℝ)| ≤ _
    rw [Int.cast_sub]
    exact abs_sub_le_of_floor_div_eq (by positivity) hcell.symm
  have hrel : |a*(m:ℝ)+b*(n:ℝ)| ≤ 2*rho := by
    have hp' := abs_le.mp (hstrip p hp)
    have hq' := abs_le.mp (hstrip q hq)
    dsimp only [m,n]
    push_cast
    apply abs_le.mpr
    constructor <;> linarith only [hp'.1,hp'.2,hq'.1,hq'.2]
  have hap : 0 < |a| := lt_of_le_of_lt (by linarith only [hrho]) ha
  have hn : n ≠ 0 := by
    intro hn0
    have hmrel : |a| *|(m:ℝ)| ≤ 2*rho := by simpa only [hn0,Int.cast_zero,mul_zero,add_zero,abs_mul] using hrel
    have hmlt : |(m:ℝ)| < 1 := (mul_lt_mul_iff_of_pos_left hap).mp
      (by simpa only [mul_one] using hmrel.trans_lt ha)
    rw [← Int.cast_abs] at hmlt
    have hm0 : m = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hmlt)
    apply hpq
    ext i
    fin_cases i <;> dsimp only [m,n] at hm0 hn0
    · exact (sub_eq_zero.mp hm0).symm
    · exact (sub_eq_zero.mp hn0).symm
  have hbn : |b*(n:ℝ)| ≤ |a| *(8*theta) := by
    rw [abs_mul]
    exact mul_le_mul hb hnabs (abs_nonneg _) (abs_nonneg _)
  have ham : |a| *|(m:ℝ)| ≤ 2*rho+|a| *(8*theta) := by
    rw [← abs_mul]
    calc
      _ ≤ |a*(m:ℝ)+b*(n:ℝ)|+|b*(n:ℝ)| := by
        simpa only [add_sub_cancel_right,sub_zero,zero_sub,abs_neg] using
          abs_sub_le (a*(m:ℝ)+b*(n:ℝ)) 0 (b*(n:ℝ))
      _ ≤ _ := add_le_add hrel hbn
  have hmabs : |(m:ℝ)| ≤ 9*theta := by
    apply (mul_le_mul_iff_of_pos_left hap).mp
    have hcoef : 8*theta+1 ≤ 9*theta := by linarith only [htheta]
    have hh := mul_le_mul_of_nonneg_left hcoef hap.le
    nlinarith only [ham,ha,hh]
  exact ⟨m,n,hn,hnabs,hmabs,hrel⟩

end WaveTurbulence.Counting
