/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Counting.IntervalCells
public import WaveTurbulence.Foundations.Counting.FiniteFibers
import Mathlib.Tactic

/-! # Actual lattice packing in a rotated shell and strip

The small-radius fiber of DH23 basiccount(5) is counted in rotated floor
cells. Rotation preserves distances, not the product integer lattice;
we count at most nine original lattice points in each rotated unit cell.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

/-- One coordinate of an actual rotated and translated lattice point. -/
def k4RotU (c s : ℝ) (b : Fin 2 → ℝ) (n : Fin 2 → ℤ) : ℝ :=
  c*((n 0 : ℝ)-b 0)+s*((n 1 : ℝ)-b 1)

/-- The perpendicular coordinate in the same actual orthogonal frame. -/
def k4RotV (c s : ℝ) (b : Fin 2 → ℝ) (n : Fin 2 → ℤ) : ℝ :=
  -s*((n 0 : ℝ)-b 0)+c*((n 1 : ℝ)-b 1)

private theorem rotated_difference_sq (c s : ℝ) (hf : c^2+s^2=1)
    (b : Fin 2 → ℝ) (n m : Fin 2 → ℤ) :
    (k4RotU c s b n-k4RotU c s b m)^2+(k4RotV c s b n-k4RotV c s b m)^2 =
      ((n 0 : ℝ)-m 0)^2+((n 1 : ℝ)-m 1)^2 := by
  calc
    _ = (c^2+s^2)*(((n 0 : ℝ)-m 0)^2+((n 1 : ℝ)-m 1)^2) := by
      unfold k4RotU k4RotV
      ring
    _ = _ := by rw [hf,one_mul]

/-- Actual integer coordinate diameters bound a planar finite set. -/
private theorem planar_card_le_nine (S : Finset (Fin 2 → ℤ))
    (hdiam : ∀ n ∈ S, ∀ m ∈ S, ∀ i, |(n i : ℝ)-m i| ≤ 2) :
    (S.card : ℝ) ≤ 9 := by
  classical
  have hp (i : Fin 2) : ((S.image (fun n => n i)).card : ℝ) ≤ 3 := by
    simpa only [show (2 : ℝ)+1=3 by norm_num] using
      Counting.card_int_finset_le_of_diameter (S.image (fun n => n i)) (by norm_num : (0 : ℝ) ≤ 2)
        (by
          intro n hn m hm
          obtain ⟨x,hx,rfl⟩ := mem_image.mp hn
          obtain ⟨y,hy,rfl⟩ := mem_image.mp hm
          exact hdiam x hx y hy i)
  have hf : ∀ z ∈ S.image (fun n => n 0), ((S.filter (fun n => n 0=z)).card : ℝ) ≤ 3 := by
    intro z _hz
    let T := S.filter (fun n => n 0=z)
    have hinj : Set.InjOn (fun n : Fin 2 → ℤ => n 1) (T : Set (Fin 2 → ℤ)) := by
      intro n hn m hm h1
      funext i
      fin_cases i
      · exact (mem_filter.mp hn).2.trans (mem_filter.mp hm).2.symm
      · exact h1
    rw [← card_image_of_injOn hinj]
    have hsub : T.image (fun n => n 1) ⊆ S.image (fun n => n 1) := by
      intro x hx
      obtain ⟨n,hn,rfl⟩ := mem_image.mp hx
      exact mem_image_of_mem _ (mem_filter.mp hn).1
    have hcard : ((T.image (fun n => n 1)).card : ℝ) ≤ ((S.image (fun n => n 1)).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    exact hcard.trans (hp 1)
  have hh := Counting.card_le_image_card_mul_of_fiber_le S (fun n => n 0) hf
  nlinarith only [hh,hp 0]

/-- One rotated unit floor cell contains at most nine actual integer points. -/
theorem k4_rotated_cell_card_le (S : Finset (Fin 2 → ℤ))
    (c s : ℝ) (hf : c^2+s^2=1) (b : Fin 2 → ℝ) (i j : ℤ)
    (hcell : ∀ n ∈ S, ⌊k4RotU c s b n⌋=i ∧ ⌊k4RotV c s b n⌋=j) :
    (S.card : ℝ) ≤ 9 := by
  apply planar_card_le_nine S
  intro n hn m hm k
  have hu : |k4RotU c s b n-k4RotU c s b m| ≤ 1 := by
    simpa only [div_one] using Counting.abs_sub_le_of_floor_div_eq (by norm_num : (0 : ℝ)<1)
      (by simpa only [div_one] using (hcell n hn).1.trans (hcell m hm).1.symm)
  have hv : |k4RotV c s b n-k4RotV c s b m| ≤ 1 := by
    simpa only [div_one] using Counting.abs_sub_le_of_floor_div_eq (by norm_num : (0 : ℝ)<1)
      (by simpa only [div_one] using (hcell n hn).2.trans (hcell m hm).2.symm)
  have hu2 : (k4RotU c s b n-k4RotU c s b m)^2 ≤ 1 := by nlinarith only [sq_abs (k4RotU c s b n-k4RotU c s b m),hu,abs_nonneg (k4RotU c s b n-k4RotU c s b m)]
  have hv2 : (k4RotV c s b n-k4RotV c s b m)^2 ≤ 1 := by nlinarith only [sq_abs (k4RotV c s b n-k4RotV c s b m),hv,abs_nonneg (k4RotV c s b n-k4RotV c s b m)]
  have he := rotated_difference_sq c s hf b n m
  have h0 := sq_nonneg ((n 0 : ℝ)-m 0)
  have h1 := sq_nonneg ((n 1 : ℝ)-m 1)
  fin_cases k
  · change |(n 0 : ℝ)-m 0| ≤ 2
    apply abs_le.mpr
    constructor <;> nlinarith only [he,hu2,hv2,h0,h1]
  · change |(n 1 : ℝ)-m 1| ≤ 2
    apply abs_le.mpr
    constructor <;> nlinarith only [he,hu2,hv2,h0,h1]

private theorem square_difference_bound {x y M : ℝ}
    (hx : |x| ≤ M) (hy : |y| ≤ M) (hxy : |x-y| ≤ 1) : |x^2-y^2| ≤ 2*M := by
  have hs : |x+y| ≤ 2*M := (abs_add_le x y).trans (by linarith only [hx,hy])
  calc
    _ = |x-y| * |x+y| := by rw [← abs_mul]; congr 1; ring
    _ ≤ 1*(2*M) := mul_le_mul hxy hs (abs_nonneg _) (by norm_num)
    _ = _ := by ring

private theorem floor_square_difference_bound {x M : ℝ} (_hM : 0 ≤ M) (hx : |x| ≤ M) :
    |(⌊x⌋ : ℝ)^2-x^2| ≤ 2*M+1 := by
  have hl := Int.floor_le x
  have hu := Int.lt_floor_add_one x
  have hd : |(⌊x⌋ : ℝ)-x| ≤ 1 := abs_le.mpr (by constructor <;> linarith only [hl,hu])
  have hf : |(⌊x⌋ : ℝ)| ≤ M+1 := by
    calc
      _ = |((⌊x⌋ : ℝ)-x)+x| := by congr 1; ring
      _ ≤ |(⌊x⌋ : ℝ)-x|+|x| := abs_add_le _ _
      _ ≤ _ := by linarith only [hd,hx]
  have hs : |(⌊x⌋ : ℝ)+x| ≤ 2*M+1 := (abs_add_le _ _).trans (by linarith only [hf,hx])
  calc
    _ = |(⌊x⌋ : ℝ)-x| * |(⌊x⌋ : ℝ)+x| := by rw [← abs_mul]; congr 1; ring
    _ ≤ 1*(2*M+1) := mul_le_mul hd hs (abs_nonneg _) (by norm_num)
    _ = _ := by ring

/-- A genuine finite planar sphere-and-strip estimate, with arbitrary
rotation and centers. M controls actual coordinates, so no invalid rotated
integer-grid argument or hidden radius bound is used. -/
theorem k4_planar_shell_strip_card_le (S : Finset (Fin 2 → ℤ))
    (c s : ℝ) (hf : c^2+s^2=1) (b : Fin 2 → ℝ)
    {A M W : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M) (hW : 0 ≤ W) (α K : ℝ)
    (hcoord : ∀ n ∈ S, |k4RotU c s b n| ≤ M ∧ |k4RotV c s b n| ≤ M)
    (hstrip : ∀ n ∈ S, |k4RotU c s b n-α| ≤ A)
    (hshell : ∀ n ∈ S, |(k4RotU c s b n)^2+(k4RotV c s b n)^2-K| ≤ W) :
    (S.card : ℝ) ≤ (2*A+2)*(2*Real.sqrt (2*(W+4*M+1))+2)*9 := by
  classical
  let U := k4RotU c s b
  let V := k4RotV c s b
  have hproj : ((S.image (fun n => ⌊U n⌋)).card : ℝ) ≤ 2*A+2 := by
    simpa only [div_one] using Counting.card_floor_cells_le S U hA (by norm_num : (0 : ℝ)<1) hstrip
  have hfib : ∀ i ∈ S.image (fun n => ⌊U n⌋),
      ((S.filter (fun n => ⌊U n⌋=i)).card : ℝ) ≤ (2*Real.sqrt (2*(W+4*M+1))+2)*9 := by
    intro i hi
    obtain ⟨n0,hn0,hni⟩ := mem_image.mp hi
    let T := S.filter (fun n => ⌊U n⌋=i)
    have hquad : ∀ j ∈ T.image (fun n => ⌊V n⌋),
        |(j : ℝ)^2+(U n0)^2-K| ≤ W+4*M+1 := by
      intro j hj
      obtain ⟨n,hn,rfl⟩ := mem_image.mp hj
      have hnS := (mem_filter.mp hn).1
      have hu : |U n-U n0| ≤ 1 := by
        simpa only [div_one] using Counting.abs_sub_le_of_floor_div_eq (by norm_num : (0 : ℝ)<1)
          (by simpa only [div_one] using (mem_filter.mp hn).2.trans hni.symm)
      have hsq := square_difference_bound (hcoord n hnS).1 (hcoord n0 hn0).1 hu
      have hfl := floor_square_difference_bound hM (hcoord n hnS).2
      have he : (⌊V n⌋ : ℝ)^2+(U n0)^2-K =
          ((⌊V n⌋ : ℝ)^2-(V n)^2) + ((U n0)^2-(U n)^2) + ((U n)^2+(V n)^2-K) := by ring
      rw [he]
      have hsq' : |(U n0)^2-(U n)^2| ≤ 2*M := by rw [abs_sub_comm]; exact hsq
      calc
        _ ≤ |(⌊V n⌋ : ℝ)^2-(V n)^2| + |(U n0)^2-(U n)^2| + |(U n)^2+(V n)^2-K| :=
          by
            have h1 := abs_add_le (((⌊V n⌋ : ℝ)^2-(V n)^2)+((U n0)^2-(U n)^2)) ((U n)^2+(V n)^2-K)
            have h2 := abs_add_le ((⌊V n⌋ : ℝ)^2-(V n)^2) ((U n0)^2-(U n)^2)
            linarith only [h1,h2]
        _ ≤ _ := by
          have hh := hshell n hnS
          change |(U n)^2+(V n)^2-K| ≤ W at hh
          linarith only [hfl,hsq',hh]
    have hq := Counting.card_quadratic_strip_le (T.image (fun n => ⌊V n⌋))
      (A := 1) (v := 0) (H := (U n0)^2) (K := K) (W := W+4*M+1)
      (by norm_num) (by positivity) (by simpa only [sub_zero,one_mul] using hquad)
    have hc : (T.card : ℝ) ≤ ((T.image (fun n => ⌊V n⌋)).card : ℝ)*9 := by
      apply Counting.card_le_image_card_mul_of_fiber_le T (fun n => ⌊V n⌋)
      intro j _hj
      apply k4_rotated_cell_card_le _ c s hf b i j
      intro n hn
      exact ⟨(mem_filter.mp (mem_filter.mp hn).1).2,(mem_filter.mp hn).2⟩
    exact hc.trans (mul_le_mul_of_nonneg_right hq (by norm_num))
  have hh := Counting.card_le_image_card_mul_of_fiber_le S (fun n => ⌊U n⌋) hfib
  have hpos : 0 ≤ (2*Real.sqrt (2*(W+4*M+1))+2)*9 := by positivity
  have hfinal := mul_le_mul_of_nonneg_right hproj hpos
  exact hh.trans (by simpa only [mul_assoc] using hfinal)

end WaveTurbulence.MoleProp
