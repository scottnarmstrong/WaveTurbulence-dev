/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ApproxNT.Partition
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# A finite smooth partition of the actual source output-time interval

The profile is the landed scalar theta1. On [0,N], all contributing
integer translates at scale h lie between -1 and ceil(N/h)+2. Each cell
is supported where the local extension agrees with the source integral.
-/

public section
open Set Finset
open scoped Classical
namespace WaveTurbulence.Sumint

/-- The finite time cells covering the entire source output-time range. -/
@[expose] noncomputable def timeCellIndices (N : ℕ) (h : ℝ) : Finset ℤ :=
  Finset.Icc (-1) (⌈(N:ℝ)/h⌉+2)

/-- The scalar smooth profile on a source time cell. -/
@[expose] noncomputable def timeCellProfile (h : ℝ) (j : ℤ) (t : ℝ) : ℝ :=
  ApproxNT.theta1 (t/h-(j:ℝ))

/-- Every possible contributing translate on [0,N] is among the fixed finite cell indices. -/
theorem theta1Support_subset_timeCellIndices (N : ℕ) {h t : ℝ} (hh : 0 < h) (ht : t ∈ Icc (0:ℝ) N) :
    ApproxNT.theta1Support (t/h) ⊆ timeCellIndices N h := by
  intro j hj
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
  have hi' : i < 4 := Finset.mem_range.mp hi
  have hf0 : 0 ≤ ⌊t/h⌋ := Int.floor_nonneg.mpr (div_nonneg ht.1 hh.le)
  have hfN : ⌊t/h⌋ ≤ ⌈(N:ℝ)/h⌉ :=
    (Int.floor_mono (div_le_div_of_nonneg_right ht.2 hh.le)).trans (Int.floor_le_ceil _)
  apply Finset.mem_Icc.mpr
  constructor <;> omega

/-- The actual smooth source time-cell profiles sum to one on the complete output-time range. -/
theorem sum_timeCellProfile (N : ℕ) {h t : ℝ} (hh : 0 < h) (ht : t ∈ Icc (0:ℝ) N) :
    ∑ j ∈ timeCellIndices N h, timeCellProfile h j t = 1 := by
  rw [← ApproxNT.sum_theta1Support (t/h)]
  symm
  apply Finset.sum_subset (theta1Support_subset_timeCellIndices N hh ht)
  intro j _ hj
  exact ApproxNT.theta1_sub_eq_zero hj

/-- Every nonzero time-cell profile lies in its actual local extension cell. -/
theorem abs_sub_cell_le_of_timeCellProfile_ne_zero {h t : ℝ} (hh : 0 < h) (j : ℤ)
    (hj : timeCellProfile h j t ≠ 0) : |t-(j:ℝ)*h| ≤ h := by
  have hab : |t/h-(j:ℝ)| < 1 := by
    by_contra! hn
    exact hj (ApproxNT.theta1_eq_zero hn)
  have he : t-(j:ℝ)*h = (t/h-(j:ℝ))*h := by field_simp
  rw [he,abs_mul,abs_of_pos hh]
  exact (mul_le_mul_of_nonneg_right hab.le hh.le).trans_eq (one_mul h)

/-- The finite time partition costs at most a fixed step-dependent constant times h inverse. -/
theorem card_timeCellIndices_le (N : ℕ) {h : ℝ} (hh : h ∈ Ioc (0:ℝ) 1) :
    ((timeCellIndices N h).card:ℝ) ≤ ((N:ℝ)+5)/h := by
  have hc0 : 0 ≤ ⌈(N:ℝ)/h⌉ := by
    simpa only [Int.ceil_zero] using Int.ceil_mono (div_nonneg (Nat.cast_nonneg N) hh.1.le)
  have hc := Int.card_Icc_of_le (-1) (⌈(N:ℝ)/h⌉+2) (by omega)
  have he : ((timeCellIndices N h).card:ℝ) = (⌈(N:ℝ)/h⌉:ℝ)+4 := by
    have hcast : ((timeCellIndices N h).card:ℝ) = ((⌈(N:ℝ)/h⌉+2:ℤ):ℝ)+1-(-1:ℤ) := by
      exact_mod_cast hc
    push_cast at hcast
    linarith only [hcast]
  rw [he]
  have hceil := Int.ceil_lt_add_one ((N:ℝ)/h)
  apply (le_div_iff₀ hh.1).mpr
  have hm := mul_lt_mul_of_pos_right hceil hh.1
  have hcancel : ((N:ℝ)/h)*h = N := div_mul_cancel₀ _ hh.1.ne'
  nlinarith only [hm,hcancel,hh.2]

/-- Each source time-cell profile is smooth at the ordinary C-infinity regularity. -/
theorem contDiff_timeCellProfile (h : ℝ) (j : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (timeCellProfile h j) :=
  ApproxNT.contDiff_theta1.comp ((contDiff_id.div_const h).sub contDiff_const)

end WaveTurbulence.Sumint
