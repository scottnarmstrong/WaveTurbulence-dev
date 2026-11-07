/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountFrame
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountSlices
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountAnnulus
import Mathlib.Tactic

/-! # Dimension lifting of the genuine K4 sphere-and-strip count

The planar coefficient and the fixed complementary contributions are the
literal projections of the original physical equations. No fiber count
or cancellation estimate is an assumption.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

/-- An actual d-dimensional shell-and-strip finite set is counted by its
literal complementary boxes and the proved planar packing estimate. -/
theorem k4_nd_shell_strip_card_le {d : ℕ} (S : Finset (Fin d → ℤ))
    (i j : Fin d) (hij : i ≠ j) (r : Mom d) (b : Fin d → ℝ)
    {A M W B T : ℝ} (hA : 0 < A) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hr : A ≤ ‖(WithLp.toLp 2 ![r i,r j] : Mom 2)‖) (α K : ℝ)
    (hbox : ∀ n ∈ S, ∀ k, |(n k : ℝ)-b k| ≤ B)
    (hball : ∀ n ∈ S, ‖latticePoint 1 n‖ ≤ M)
    (hstrip : ∀ n ∈ S, |inner ℝ r (latticePoint 1 n)-α| ≤ T)
    (hshell : ∀ n ∈ S, |‖latticePoint 1 n‖^2-K| ≤ W) :
    (S.card : ℝ) ≤ (2*B+1)^(d-2)*((2*(T/A)+2)*(2*Real.sqrt (2*(W+4*M+1))+2)*9) := by
  classical
  let C := (2*(T/A)+2)*(2*Real.sqrt (2*(W+4*M+1))+2)*9
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hproj := k4_tail_projection_card_le S i j hij b hB hbox
  have hfib : ∀ t ∈ S.image (k4Tail i j),
      ((S.filter (fun n => k4Tail i j n=t)).card : ℝ) ≤ C := by
    intro t _ht
    rw [← card_k4PlaneSlice]
    apply k4_planar_physical_shell_strip_le (k4PlaneSlice S i j t)
      (WithLp.toLp 2 ![r i,r j]) 0 hA hM hT hW hr
      (α-∑ k : K4TailIndex i j, r k*(t k : ℝ))
      (K-∑ k : K4TailIndex i j, (t k : ℝ)^2)
    · intro p hp
      obtain ⟨n,hn,rfl⟩ := mem_image.mp hp
      have hnS := (mem_filter.mp hn).1
      have he := k4_plane_norm_sq i j hij n
      have ht0 : 0 ≤ ∑ k : K4TailIndex i j, (n k : ℝ)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
      have hf0 := norm_nonneg (latticePoint 1 n)
      have hp0 := norm_nonneg (latticePoint 1 (k4Plane i j n))
      have hb := hball n hnS
      rw [sub_zero]
      nlinarith only [he,ht0,hf0,hp0,hb,hM]
    · intro p hp
      obtain ⟨n,hn,rfl⟩ := mem_image.mp hp
      have hnt : ∀ k : K4TailIndex i j, n k=t k := fun k => congrFun (mem_filter.mp hn).2 k
      have he := k4_plane_inner i j hij r n
      simp only [hnt] at he
      have hs := hstrip n (mem_filter.mp hn).1
      rw [he] at hs
      rw [sub_zero]
      convert hs using 1 <;> congr 1 <;> ring
    · intro p hp
      obtain ⟨n,hn,rfl⟩ := mem_image.mp hp
      have hnt : ∀ k : K4TailIndex i j, n k=t k := fun k => congrFun (mem_filter.mp hn).2 k
      have he := k4_plane_norm_sq i j hij n
      simp only [hnt] at he
      have hs := hshell n (mem_filter.mp hn).1
      rw [he] at hs
      rw [sub_zero]
      convert hs using 1 <;> congr 1 <;> ring
  have hh := Counting.card_le_image_card_mul_of_fiber_le S (k4Tail i j) hfib
  exact hh.trans (mul_le_mul_of_nonneg_right hproj hC)

/-- An actual large-radius planar slice in dimension d is controlled by
the proved local annulus bound, with arbitrary coordinate-box center. -/
theorem k4_nd_large_shell_card_le {d : ℕ} (S : Finset (Fin d → ℤ))
    (i j : Fin d) (hij : i ≠ j) (b : Fin d → ℝ)
    {M W B K : ℝ} (hM : 0 < M) (hW : 1 ≤ W) (hMW : 4*W ≤ M^2) (hB : 0 ≤ B)
    (hbox : ∀ n ∈ S, ∀ k, |(n k : ℝ)-b k| ≤ B)
    (hlarge : ∀ n ∈ S, M ≤ ‖latticePoint 1 (k4Plane i j n)‖)
    (hshell : ∀ n ∈ S, |‖latticePoint 1 n‖^2-K| ≤ W) :
    (S.card : ℝ) ≤ (2*B+1)^(d-2)*
      (640000*(Real.sqrt W+(2*B)*W^((3 : ℝ)/2)/(M/2)+
        (2*B)*Real.sqrt W*(M/2)^(-((1 : ℝ)/3)))) := by
  classical
  let C := 640000*(Real.sqrt W+(2*B)*W^((3 : ℝ)/2)/(M/2)+
    (2*B)*Real.sqrt W*(M/2)^(-((1 : ℝ)/3)))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hproj := k4_tail_projection_card_le S i j hij b hB hbox
  have hfib : ∀ t ∈ S.image (k4Tail i j),
      ((S.filter (fun n => k4Tail i j n=t)).card : ℝ) ≤ C := by
    intro t _ht
    rw [← card_k4PlaneSlice]
    rcases (k4PlaneSlice S i j t).eq_empty_or_nonempty with he | hne
    · rw [he,card_empty,Nat.cast_zero]
      exact hC
    apply k4_large_shell_radius_le (k4PlaneSlice S i j t) hne 0
      (WithLp.toLp 2 ![b i,b j]) (K := K-∑ k : K4TailIndex i j, (t k : ℝ)^2)
      hM hW hMW (mul_nonneg (by norm_num) hB)
    · intro p hp
      obtain ⟨n,hn,rfl⟩ := mem_image.mp hp
      have hnS := (mem_filter.mp hn).1
      have hnt : ∀ k : K4TailIndex i j, n k=t k := fun k => congrFun (mem_filter.mp hn).2 k
      have he := k4_plane_norm_sq i j hij n
      simp only [hnt] at he
      refine ⟨by rw [sub_zero]; exact hlarge n hnS,?_⟩
      have hs := hshell n hnS
      rw [he] at hs
      rw [sub_zero]
      convert hs using 1 <;> congr 1 <;> ring
    · intro p hp
      obtain ⟨n,hn,rfl⟩ := mem_image.mp hp
      have hnS := (mem_filter.mp hn).1
      have hi := hbox n hnS i
      have hj := hbox n hnS j
      have hi2 : ((n i : ℝ)-b i)^2 ≤ B^2 := by nlinarith only [hi,abs_nonneg ((n i : ℝ)-b i),sq_abs ((n i : ℝ)-b i)]
      have hj2 : ((n j : ℝ)-b j)^2 ≤ B^2 := by nlinarith only [hj,abs_nonneg ((n j : ℝ)-b j),sq_abs ((n j : ℝ)-b j)]
      have he : ‖latticePoint 1 (k4Plane i j n)-(WithLp.toLp 2 ![b i,b j] : Mom 2)‖^2 =
          ((n i : ℝ)-b i)^2+((n j : ℝ)-b j)^2 := by
        simp only [EuclideanSpace.real_norm_sq_eq,latticePoint,PiLp.sub_apply,div_one,
          Fin.sum_univ_two,k4Plane,Matrix.cons_val_zero,Matrix.cons_val_one]
      have hn0 := norm_nonneg (latticePoint 1 (k4Plane i j n)-(WithLp.toLp 2 ![b i,b j] : Mom 2))
      nlinarith only [he,hi2,hj2,hn0,hB]
  have hh := Counting.card_le_image_card_mul_of_fiber_le S (k4Tail i j) hfib
  exact hh.trans (mul_le_mul_of_nonneg_right hproj hC)

private theorem k4_exists_second_coordinate {d : ℕ} (hd : 2 ≤ d) (i : Fin d) :
    ∃ j : Fin d, i ≠ j := by
  let z : Fin d := ⟨0,by omega⟩
  let o : Fin d := ⟨1,by omega⟩
  by_cases hi : i=z
  · refine ⟨o,?_⟩
    intro he
    have hv := congrArg Fin.val (hi.symm.trans he)
    change (0 : ℕ)=1 at hv
    omega
  · exact ⟨z,hi⟩

/-- The needed two-coordinate strip coefficient is selected internally
from the actual norm lower bound. -/
theorem k4_nd_shell_strip_norm_card_le {d : ℕ} (hd : 2 ≤ d)
    (S : Finset (Fin d → ℤ)) (r : Mom d) (b : Fin d → ℝ)
    {A M W B T : ℝ} (hA : 0 < A) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (hB : 0 ≤ B) (hT : 0 ≤ T) (hr : A ≤ ‖r‖) (α K : ℝ)
    (hbox : ∀ n ∈ S, ∀ k, |(n k : ℝ)-b k| ≤ B)
    (hball : ∀ n ∈ S, ‖latticePoint 1 n‖ ≤ M)
    (hstrip : ∀ n ∈ S, |inner ℝ r (latticePoint 1 n)-α| ≤ T)
    (hshell : ∀ n ∈ S, |‖latticePoint 1 n‖^2-K| ≤ W) :
    (S.card : ℝ) ≤ (2*B+1)^(d-2)*
      ((2*((d : ℝ)*T/A)+2)*(2*Real.sqrt (2*(W+4*M+1))+2)*9) := by
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  obtain ⟨i,hi⟩ := CountLemmas.exists_large_coordinate hd0 r
  obtain ⟨j,hij⟩ := k4_exists_second_coordinate hd i
  have hri : A/(d : ℝ) ≤ |r i| := by
    apply (div_le_iff₀ hdR).mpr
    simpa only [mul_comm] using hr.trans hi
  have hrp : |r i| ≤ ‖(WithLp.toLp 2 ![r i,r j] : Mom 2)‖ := by
    simpa only [Real.norm_eq_abs,Matrix.cons_val_zero] using
      PiLp.norm_apply_le (WithLp.toLp 2 ![r i,r j] : Mom 2) 0
  have hh := k4_nd_shell_strip_card_le S i j hij r b (div_pos hA hdR) hM hW hB hT
    (hri.trans hrp) α K hbox hball hstrip hshell
  have he : T/(A/(d : ℝ)) = (d : ℝ)*T/A := by field_simp [hA.ne',hdR.ne'] <;> ring
  simpa only [he] using hh

/-- A full large-radius shell is covered by actual coordinate slices;
the large planar coordinate is selected by finite covering, not assumed. -/
theorem k4_nd_large_shell_norm_card_le {d : ℕ} (hd : 2 ≤ d)
    (S : Finset (Fin d → ℤ)) (b : Fin d → ℝ)
    {M W B K : ℝ} (hM : 0 < M) (hW : 1 ≤ W)
    (hMW : 4*W ≤ (M/(d : ℝ))^2) (hB : 0 ≤ B)
    (hbox : ∀ n ∈ S, ∀ k, |(n k : ℝ)-b k| ≤ B)
    (hlarge : ∀ n ∈ S, M ≤ ‖latticePoint 1 n‖)
    (hshell : ∀ n ∈ S, |‖latticePoint 1 n‖^2-K| ≤ W) :
    (S.card : ℝ) ≤ (d : ℝ)*((2*B+1)^(d-2)*
      (640000*(Real.sqrt W+(2*B)*W^((3 : ℝ)/2)/((M/(d : ℝ))/2)+
        (2*B)*Real.sqrt W*((M/(d : ℝ))/2)^(-((1 : ℝ)/3))))) := by
  classical
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  let F := fun i : Fin d => S.filter (fun n => M/(d : ℝ) ≤ |(n i : ℝ)|)
  have hcover : S ⊆ univ.biUnion F := by
    intro n hn
    obtain ⟨i,hi⟩ := CountLemmas.exists_large_coordinate hd0 (latticePoint 1 n)
    have hni : M/(d : ℝ) ≤ |(n i : ℝ)| := by
      apply (div_le_iff₀ hdR).mpr
      have hh := (hlarge n hn).trans hi
      simpa only [latticePoint,div_one,mul_comm] using hh
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨hn,hni⟩⟩
  have hc : (S.card : ℝ) ≤ ∑ i : Fin d, ((F i).card : ℝ) := by
    exact_mod_cast (card_le_card hcover).trans (card_biUnion_le (s := (univ : Finset (Fin d))) (t := F))
  have hf (i : Fin d) : ((F i).card : ℝ) ≤ (2*B+1)^(d-2)*
      (640000*(Real.sqrt W+(2*B)*W^((3 : ℝ)/2)/((M/(d : ℝ))/2)+
        (2*B)*Real.sqrt W*((M/(d : ℝ))/2)^(-((1 : ℝ)/3)))) := by
    obtain ⟨j,hij⟩ := k4_exists_second_coordinate hd i
    apply k4_nd_large_shell_card_le (F i) i j hij b (div_pos hM hdR) hW hMW hB
    · intro n hn k
      exact hbox n (mem_filter.mp hn).1 k
    · intro n hn
      have hp : |(n i : ℝ)| ≤ ‖latticePoint 1 (k4Plane i j n)‖ := by
        simpa only [Real.norm_eq_abs,latticePoint,div_one,k4Plane,Matrix.cons_val_zero] using
          PiLp.norm_apply_le (latticePoint 1 (k4Plane i j n)) 0
      exact (mem_filter.mp hn).2.trans hp
    · intro n hn
      exact hshell n (mem_filter.mp hn).1
  have hh := sum_le_sum (s := (univ : Finset (Fin d))) (fun i _ => hf i)
  exact hc.trans (by simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] using hh)

end WaveTurbulence.MoleProp
