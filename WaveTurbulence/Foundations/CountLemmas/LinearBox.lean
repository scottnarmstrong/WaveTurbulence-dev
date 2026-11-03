/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Counting.LatticeBox
public import WaveTurbulence.Foundations.Counting.FiniteFibers
public import WaveTurbulence.Foundations.Counting.LinearStrip

/-! # Coordinate slicing for lattice strips -/

public section
open Finset
namespace WaveTurbulence.CountLemmas

/-- Fixing all coordinates except `i` leaves at most the one-dimensional
strip count. The box and the linear level have arbitrary real centers. -/
theorem card_linear_box_le {d : ℕ} (s : Finset (Fin d → ℤ))
    (c a : Fin d → ℝ) (i : Fin d) {R ρ β : ℝ}
    (hR : 0 ≤ R) (hρ : 0 ≤ ρ) (hai : a i ≠ 0)
    (hbox : ∀ n ∈ s, ∀ j, |(n j : ℝ)-c j| ≤ R)
    (hstrip : ∀ n ∈ s, |(∑ j, a j*(n j : ℝ))-β| ≤ ρ) :
    (s.card : ℝ) ≤ (2*R+1)^(d-1)*(2*ρ/|a i|+1) := by
  classical
  let f := fun n : Fin d → ℤ => fun j : {j : Fin d // j ≠ i} => n j
  have hproj : ((s.image f).card : ℝ) ≤ (2*R+1)^(d-1) := by
    let B := Fintype.piFinset (fun j : {j : Fin d // j ≠ i} =>
      Counting.integerInterval (c j-R) (c j+R))
    have hsub : s.image f ⊆ B := by
      intro z hz
      obtain ⟨n,hn,rfl⟩ := mem_image.mp hz
      apply Fintype.mem_piFinset.mpr
      intro j
      have hh := abs_le.mp (hbox n hn j)
      apply (Counting.mem_integerInterval _ _ _).mpr
      constructor <;> linarith only [hh.1,hh.2]
    have hc : ((s.image f).card : ℝ) ≤ (B.card : ℝ) := by
      exact_mod_cast card_le_card hsub
    apply hc.trans
    rw [show (B.card : ℝ) = ∏ j : {j : Fin d // j ≠ i},
      ((Counting.integerInterval (c j-R) (c j+R)).card : ℝ) from by
        simp only [B,Fintype.card_piFinset,Nat.cast_prod]]
    calc
      _ ≤ ∏ _j : {j : Fin d // j ≠ i}, (2*R+1) := prod_le_prod₀
        (fun _ _ => Nat.cast_nonneg _) (fun j _ => Counting.card_integerInterval_le (c j) hR)
      _ = _ := by
        simp only [prod_const,card_univ,Fintype.card_subtype_compl,
          Fintype.card_unique,Fintype.card_fin]
  have hfib : ∀ z ∈ s.image f,
      (((s.filter (fun n => f n = z)).card) : ℝ) ≤ 2*ρ/|a i|+1 := by
    intro z hz
    let t := s.filter (fun n => f n = z)
    have heq {n m : Fin d → ℤ} (hn : n ∈ t) (hm : m ∈ t) (j : Fin d) (hj : j ≠ i) :
        n j = m j := by
      have hh := (mem_filter.mp hn).2.trans (mem_filter.mp hm).2.symm
      exact congrFun hh ⟨j,hj⟩
    have hinj : Set.InjOn (fun n : Fin d → ℤ => n i) (t : Set (Fin d → ℤ)) := by
      intro n hn m hm hnm
      funext j
      by_cases hj : j = i
      · simpa only [hj] using hnm
      · exact heq hn hm j hj
    rw [← card_image_of_injOn hinj]
    apply Counting.card_int_finset_le_of_diameter _ (by positivity : 0 ≤ 2*ρ/|a i|)
    intro x hx y hy
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hx
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hy
    have hd : (∑ j, a j*(n j : ℝ))-(∑ j, a j*(m j : ℝ)) =
        a i*((n i : ℝ)-m i) := by
      rw [← sum_sub_distrib]
      rw [sum_eq_single i]
      · ring
      · intro j _ hji
        rw [heq hn hm j hji,sub_self]
      · intro hi
        exact (hi (mem_univ i)).elim
    have hn' := abs_le.mp (hstrip n (mem_filter.mp hn).1)
    have hm' := abs_le.mp (hstrip m (mem_filter.mp hm).1)
    have hab : |a i*((n i : ℝ)-m i)| ≤ 2*ρ := by
      rw [← hd]
      apply abs_le.mpr
      constructor <;> linarith only [hn'.1,hn'.2,hm'.1,hm'.2]
    apply (le_div_iff₀ (abs_pos.mpr hai)).mpr
    simpa only [abs_mul,mul_comm] using hab
  have hc := Counting.card_le_image_card_mul_of_fiber_le s f hfib
  exact hc.trans (mul_le_mul_of_nonneg_right hproj (by positivity))

end WaveTurbulence.CountLemmas
