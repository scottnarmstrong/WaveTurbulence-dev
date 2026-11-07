/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountHarmonic
public import WaveTurbulence.Foundations.CountLemmas.DotStrip
import Mathlib.Tactic

/-! # Localized K4 base pairs with an arbitrary translated coefficient ball

The elementary coordinate-strip bound retains both its volume term and
its lattice boundary term. A logarithmic reciprocal-coordinate sum is
uniform in the ball center. The full triple bound is used separately when
the boundary term would be too large.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
open CountLemmas

/-- Actual coefficient vectors in one fixed-coordinate fiber have only
`d−1` free integer coordinates. -/
theorem k4_ball_coordinate_fiber_le {d : ℕ} (T : Finset (Fin d → ℤ))
    {L R : ℝ} (hL : 0 < L) (hR : 0 ≤ R) (b : Mom d) (i : Fin d) (m : ℤ)
    (hball : ∀ y ∈ T, ‖latticePoint L y-b‖ ≤ R)
    (hcoord : ∀ y ∈ T, y i=m) :
    (T.card : ℝ) ≤ (2*(L*R)+1)^(d-1) := by
  have hc := card_linear_box_le T (fun j => L*b j) (fun j => if j=i then 1 else 0) i
    (mul_nonneg hL.le hR) (le_refl (0 : ℝ)) (by simp)
    (fun y hy j => coordinate_bound_of_ball hL b y (hball y hy) j)
    (β := (m : ℝ)) (by
      intro y hy
      simp only [ite_mul,one_mul,zero_mul,sum_ite_eq',mem_univ,ite_true,hcoord y hy,sub_self,abs_zero]
      exact le_rfl)
  simpa using hc

/-- One nonzero coefficient coordinate gives a genuine localized pair
count. All spatial and energy centers remain arbitrary. -/
theorem k4_localized_pair_coordinate_le {d : ℕ}
    (S : Finset ((Fin d → ℤ) × (Fin d → ℤ)))
    {L R τ : ℝ} (hL : 0 < L) (hR : 0 ≤ R) (hτ : 0 ≤ τ)
    (a b : Mom d) (α : ℝ) (i : Fin d)
    (hS : ∀ q ∈ S, NearLattice L a q.1 ∧ ‖latticePoint L q.2-b‖ ≤ R ∧
      q.2 i ≠ 0 ∧ |inner ℝ (latticePoint L q.2) (latticePoint L q.1)-α| ≤ τ) :
    (S.card : ℝ) ≤ (2*(L*R)+1)^(d-1)*(2*L+1)^(d-1)*
      (2*τ*L^2*(3+2*Real.log (⌈2*(L*R)+1⌉₊ : ℝ))+(2*(L*R)+1)) := by
  classical
  let p := fun q : (Fin d → ℤ) × (Fin d → ℤ) => q.2 i
  let J := S.image p
  have hdiam : ∀ m ∈ J, ∀ n ∈ J, |(m : ℝ)-n| ≤ 2*(L*R) := by
    intro m hm n hn
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hm
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hn
    have hx' := coordinate_bound_of_ball hL b x.2 (hS x hx).2.1 i
    have hy' := coordinate_bound_of_ball hL b y.2 (hS y hy).2.1 i
    calc
      _ = |((x.2 i : ℝ)-L*b i)-((y.2 i : ℝ)-L*b i)| := by congr 1; ring
      _ ≤ |(x.2 i : ℝ)-L*b i|+|(y.2 i : ℝ)-L*b i| := abs_sub _ _
      _ ≤ _ := by linarith only [hx',hy']
  have hJcard : (J.card : ℝ) ≤ 2*(L*R)+1 :=
    Counting.card_int_finset_le_of_diameter J (by positivity) hdiam
  have hJsum := k4_sum_inv_abs_le_log J (by positivity : 0 ≤ 2*(L*R)) hdiam
  let B := (2*(L*R)+1)^(d-1)*(2*L+1)^(d-1)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hfib : ∀ m ∈ J, ((S.filter (fun q => p q=m)).card : ℝ) ≤ B*(2*τ*L^2*|(m : ℝ)|⁻¹+1) := by
    intro m hm
    have hm0 : m ≠ 0 := by
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hm
      exact (hS q hq).2.2.1
    let T := S.filter (fun q => p q=m)
    have hproj : ((T.image Prod.snd).card : ℝ) ≤ (2*(L*R)+1)^(d-1) := by
      apply k4_ball_coordinate_fiber_le _ hL hR b i m
      · intro y hy
        obtain ⟨q,hq,rfl⟩ := mem_image.mp hy
        exact (hS q (mem_filter.mp hq).1).2.1
      · intro y hy
        obtain ⟨q,hq,rfl⟩ := mem_image.mp hy
        exact (mem_filter.mp hq).2
    have hxcard : ∀ y ∈ T.image Prod.snd,
        ((T.filter (fun q => q.2=y)).card : ℝ) ≤ (2*L+1)^(d-1)*(2*τ*L^2*|(m : ℝ)|⁻¹+1) := by
      intro y hy
      obtain ⟨q,hq,hqy⟩ := mem_image.mp hy
      have hym : y i=m := by rw [← hqy]; exact (mem_filter.mp hq).2
      let F := T.filter (fun q => q.2=y)
      have hinj : Set.InjOn Prod.fst (F : Set ((Fin d → ℤ) × (Fin d → ℤ))) := by
        intro q hq t ht he
        exact Prod.ext he ((mem_filter.mp hq).2.trans (mem_filter.mp ht).2.symm)
      rw [← card_image_of_injOn hinj]
      have hri : (latticePoint L y) i ≠ 0 := by
        change (y i : ℝ)/L ≠ 0
        rw [hym]
        exact div_ne_zero (by exact_mod_cast hm0) hL.ne'
      have hc := card_dot_strip_ball_le (F.image Prod.fst) hL (by norm_num : (0 : ℝ)≤1) hτ
        a (latticePoint L y) α i hri
        (by
          intro x hx
          obtain ⟨q,hq,rfl⟩ := mem_image.mp hx
          exact (hS q (mem_filter.mp (mem_filter.mp hq).1).1).1)
        (by
          intro x hx
          obtain ⟨q,hq,rfl⟩ := mem_image.mp hx
          have he := (hS q (mem_filter.mp (mem_filter.mp hq).1).1).2.2.2
          rw [(mem_filter.mp hq).2] at he
          exact he)
      have hfrac : 2*τ*L/|(latticePoint L y) i| = 2*τ*L^2*|(m : ℝ)|⁻¹ := by
        change 2*τ*L/|(y i : ℝ)/L| = _
        rw [hym,abs_div,abs_of_pos hL]
        field_simp <;> ring
      simpa only [mul_one,hfrac] using hc
    have hh := Counting.card_le_image_card_mul_of_fiber_le T Prod.snd hxcard
    have hm : 0 ≤ (2*L+1)^(d-1)*(2*τ*L^2*|(m : ℝ)|⁻¹+1) := by positivity
    exact hh.trans (by simpa only [B,mul_assoc] using mul_le_mul_of_nonneg_right hproj hm)
  have hsum : (S.card : ℝ) ≤ ∑ m ∈ J, B*(2*τ*L^2*|(m : ℝ)|⁻¹+1) := by
    have he := card_eq_sum_card_image p S
    have heR : (S.card : ℝ) = ∑ m ∈ J, ((S.filter (fun q => p q=m)).card : ℝ) := by exact_mod_cast he
    rw [heR]
    exact sum_le_sum hfib
  have he : (∑ m ∈ J, B*(2*τ*L^2*|(m : ℝ)|⁻¹+1)) =
      B*(2*τ*L^2*(∑ m ∈ J, |(m : ℝ)|⁻¹)+(J.card : ℝ)) := by
    simp only [mul_add,sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul]
    ring
  rw [he] at hsum
  exact hsum.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hJsum (by positivity)) hJcard) hB)

/-- Summing over the actual nonzero coefficient coordinates yields the
localized base count without choosing a conclusion-shaped dominant axis. -/
theorem k4_localized_pair_le {d : ℕ}
    (S : Finset ((Fin d → ℤ) × (Fin d → ℤ)))
    {L R τ : ℝ} (hL : 0 < L) (hR : 0 ≤ R) (hτ : 0 ≤ τ)
    (a b : Mom d) (α : ℝ)
    (hS : ∀ q ∈ S, NearLattice L a q.1 ∧ ‖latticePoint L q.2-b‖ ≤ R ∧
      q.2 ≠ 0 ∧ |inner ℝ (latticePoint L q.2) (latticePoint L q.1)-α| ≤ τ) :
    (S.card : ℝ) ≤ (d : ℝ)*((2*(L*R)+1)^(d-1)*(2*L+1)^(d-1)*
      (2*τ*L^2*(3+2*Real.log (⌈2*(L*R)+1⌉₊ : ℝ))+(2*(L*R)+1))) := by
  classical
  let F := fun i : Fin d => S.filter (fun q => q.2 i ≠ 0)
  have hcover : S ⊆ univ.biUnion F := by
    intro q hq
    have hex : ∃ i, q.2 i ≠ 0 := by
      by_contra hn
      apply (hS q hq).2.2.1
      funext i
      by_contra hi
      exact hn ⟨i,hi⟩
    obtain ⟨i,hi⟩ := hex
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨hq,hi⟩⟩
  have hc : (S.card : ℝ) ≤ ∑ i : Fin d, ((F i).card : ℝ) := by
    exact_mod_cast (card_le_card hcover).trans (card_biUnion_le (s := (univ : Finset (Fin d))) (t := F))
  have hf (i : Fin d) := k4_localized_pair_coordinate_le (F i) hL hR hτ a b α i
    (by
      intro q hq
      have hs := hS q (mem_filter.mp hq).1
      exact ⟨hs.1,hs.2.1,(mem_filter.mp hq).2,hs.2.2.2⟩)
  have hfinal := sum_le_sum (s := (univ : Finset (Fin d))) (fun i _ => hf i)
  exact hc.trans (by simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] using hfinal)

end WaveTurbulence.MoleProp
