/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.ImprovedSquaredShellThreshold
public import WaveTurbulence.Foundations.Counting.LatticeCoordinates
public import WaveTurbulence.Foundations.Counting.FiniteFibers

/-! # Lifting planar shell counts by exact coordinate fibers -/

public section
open Finset
namespace WaveTurbulence.CountLemmas

/-- A squared-energy shell in dimension `d+2`, with arbitrary real center,
inside an arbitrary coordinate box. Only the first two coordinates use the
annulus estimate; all remaining coordinates are counted exactly as fibers. -/
theorem card_squared_shell_improved_threshold_le {d : ℕ} (s : Finset (Fin (d+2) → ℤ))
    (c : Mom (d+2)) (b : Fin (d+2) → ℝ) {K W R U : ℝ}
    (hW : 1 ≤ W) (hR : 0 ≤ R) (hWU : W ≤ U) (hbudget : R^2*W ≤ U^((244 : ℝ)/81))
    (hbox : ∀ n ∈ s, ∀ i, |(n i : ℝ)-b i| ≤ R)
    (hband : ∀ n ∈ s, |‖latticePoint 1 n-c‖^2-K| ≤ W) :
    (s.card : ℝ) ≤ (2*R+1)^d*(6*Real.pi+3*|VdCB.circleDiscrepancyConstant|+1924002)*U := by
  classical
  let f := fun n : Fin (d+2) → ℤ => fun j : Fin d => n j.succ.succ
  have hproj : ((s.image f).card : ℝ) ≤ (2*R+1)^d :=
    Counting.card_le_of_coordinate_bounds (s.image f) (fun j => b j.succ.succ) hR (by
      intro z hz j
      obtain ⟨n,hn,rfl⟩ := mem_image.mp hz
      exact hbox n hn j.succ.succ)
  have hfib : ∀ z ∈ s.image f,
      (((s.filter (fun n => f n = z)).card) : ℝ) ≤ (6*Real.pi+3*|VdCB.circleDiscrepancyConstant|+1924002)*U := by
    intro z hz
    let t := s.filter (fun n => f n = z)
    let g := fun n : Fin (d+2) → ℤ => ![n 0,n 1]
    have hinj : Set.InjOn g (t : Set (Fin (d+2) → ℤ)) := by
      intro n hn m hm he
      apply (Counting.latticeSplitTwo d).injective
      apply Prod.ext he
      exact (mem_filter.mp hn).2.trans (mem_filter.mp hm).2.symm
    rw [← card_image_of_injOn hinj]
    let c₂ : Mom 2 := WithLp.toLp 2 ![c 0,c 1]
    apply card_planar_squared_shell_improved_threshold_le (t.image g) c₂ ![b 0,b 1]
      (K := K-∑ j : Fin d, ((z j : ℝ)-c j.succ.succ)^2) hW hR hWU hbudget
    · intro p hp i
      obtain ⟨n,hn,rfl⟩ := mem_image.mp hp
      fin_cases i
      · exact hbox n (mem_filter.mp hn).1 0
      · exact hbox n (mem_filter.mp hn).1 1
    · intro p hp
      obtain ⟨n,hn,rfl⟩ := mem_image.mp hp
      have htail : ∀ j : Fin d, n j.succ.succ = z j :=
        fun j => congrFun (mem_filter.mp hn).2 j
      have hid : ‖latticePoint 1 n-c‖^2 = ‖latticePoint 1 (g n)-c₂‖^2+
          ∑ j : Fin d, ((z j : ℝ)-c j.succ.succ)^2 := by
        simp only [EuclideanSpace.real_norm_sq_eq,latticePoint,PiLp.sub_apply,div_one]
        rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
        have h01 : Fin.succ (0 : Fin (d+1)) = (1 : Fin (d+2)) := rfl
        rw [h01]
        simp only [g,c₂,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
          htail]
        ring
      have hh := hband n (mem_filter.mp hn).1
      rw [hid] at hh
      convert hh using 2
      ring
  have hU : 0 ≤ U := (le_trans zero_le_one hW).trans hWU
  have hc := Counting.card_le_image_card_mul_of_fiber_le s f hfib
  calc
    _ ≤ ((s.image f).card : ℝ)*((6*Real.pi+3*|VdCB.circleDiscrepancyConstant|+1924002)*U) := hc
    _ ≤ (2*R+1)^d*((6*Real.pi+3*|VdCB.circleDiscrepancyConstant|+1924002)*U) :=
      mul_le_mul_of_nonneg_right hproj (by positivity)
    _ = _ := by ring

end WaveTurbulence.CountLemmas
