/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Frozen.Defs.LatticePoint

/-! # A dominant Euclidean coordinate and lattice separation -/

public section
open Finset
namespace WaveTurbulence.CountLemmas

/-- A Euclidean vector has a coordinate at least its norm divided by `d`.
The deliberately coarse dimension factor avoids square-root constants. -/
theorem exists_large_coordinate {d : ℕ} (hd : 0 < d) (x : Mom d) :
    ∃ i : Fin d, ‖x‖ ≤ (d : ℝ)*|x i| := by
  classical
  have hne : (univ : Finset (Fin d)).Nonempty := ⟨⟨0,hd⟩,mem_univ _⟩
  obtain ⟨i,_,hi⟩ := exists_max_image univ (fun j => |x j|) hne
  refine ⟨i,?_⟩
  have hsq : ‖x‖^2 ≤ (d : ℝ)*|x i|^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _j : Fin d, |x i|^2 := sum_le_sum (by
        intro j _
        have hh := hi j (mem_univ j)
        nlinarith only [hh,abs_nonneg (x j),abs_nonneg (x i),sq_abs (x j)])
      _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hm := mul_nonneg (by linarith only [hd1] : 0 ≤ (d : ℝ)-1)
    (mul_nonneg (Nat.cast_nonneg d) (sq_nonneg |x i|))
  have hn : 0 ≤ (d : ℝ)*|x i| := mul_nonneg (Nat.cast_nonneg d) (abs_nonneg _)
  nlinarith only [hsq,hm,hn,norm_nonneg x]

/-- A nonzero integer vector has a coordinate separated from zero by one
lattice spacing. -/
theorem exists_lattice_coordinate_gap {d : ℕ} {L : ℝ} (hL : 0 < L)
    (n : Fin d → ℤ) (hn : n ≠ 0) :
    ∃ i : Fin d, L⁻¹ ≤ |latticePoint L n i| := by
  obtain ⟨i,hi⟩ : ∃ i, n i ≠ 0 := by
    by_contra h
    apply hn
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  refine ⟨i,?_⟩
  have habs : (1 : ℝ) ≤ |(n i : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hi)
  change L⁻¹ ≤ |(n i : ℝ)/L|
  rw [abs_div,abs_of_pos hL]
  simpa only [one_div] using div_le_div_of_nonneg_right habs hL.le

end WaveTurbulence.CountLemmas
