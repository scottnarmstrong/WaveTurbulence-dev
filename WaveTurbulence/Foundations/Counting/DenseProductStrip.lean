/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.DenseStrip
public import WaveTurbulence.Foundations.Counting.LatticeBox
public import WaveTurbulence.Foundations.Counting.FiniteFibers
import Mathlib.Tactic

/-!
# Fixing the remaining coordinates of a dense strip

DH23 `basiccount0pre` (2), TeX L2045: fixing the last coordinates loses only
a dimension-dependent constant in the planar density. The remaining term
in the linear form is represented by its actual value `F z` on a fixed fiber.
-/

public section

namespace WaveTurbulence.Counting

/-- The short-relation pigeonhole step for a planar strip with `d` further
integer coordinates. All coordinate fibers and their densities are proved. -/
theorem exists_small_relation_of_dense_product_strip {d : ℕ}
    (s : Finset ((Fin 2 → ℤ) × (Fin d → ℤ))) (F : (Fin d → ℤ) → ℝ)
    (c : Fin d → ℝ) {a b alpha rho theta L v : ℝ}
    (hrho : 0 ≤ rho) (htheta : 1 ≤ theta) (hL : 16*((3:ℝ)^d*theta) ≤ L)
    (ha : 2*rho < |a|) (hb : |b| ≤ |a|)
    (hproj : ∀ n ∈ s, |(n.1 1:ℝ)-v| ≤ L)
    (hrest : ∀ n ∈ s, ∀ i, |(n.2 i:ℝ)-c i| ≤ L)
    (hstrip : ∀ n ∈ s, |a*(n.1 0:ℝ)+b*(n.1 1:ℝ)+F n.2-alpha| ≤ rho)
    (hdense : L^(d+1)/theta ≤ (s.card:ℝ)) :
    ∃ m n : ℤ, n ≠ 0 ∧ |(n:ℝ)| ≤ 8*((3:ℝ)^d*theta) ∧
      |(m:ℝ)| ≤ 9*((3:ℝ)^d*theta) ∧ |a*(m:ℝ)+b*(n:ℝ)| ≤ 2*rho := by
  classical
  have hp3 : 1 ≤ (3:ℝ)^d := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one (by norm_num : (1:ℝ) ≤ 3) d
  have htheta' : 1 ≤ (3:ℝ)^d*theta := le_trans htheta
    (by nlinarith only [hp3,htheta])
  have hL1 : 1 ≤ L := by linarith only [hL,htheta']
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have htp : 0 < theta := lt_of_lt_of_le zero_lt_one htheta
  have hthetap : 0 < (3:ℝ)^d*theta := lt_of_lt_of_le zero_lt_one htheta'
  have hs : s.Nonempty := by
    have hc : 0 < (s.card:ℝ) := (div_pos (pow_pos hLp (d+1)) htp).trans_le hdense
    exact Finset.card_pos.mp (by exact_mod_cast hc)
  have hprojcount : ((s.image Prod.snd).card:ℝ) ≤ (3*L)^d := by
    apply (card_le_of_coordinate_bounds (s.image Prod.snd) c hLp.le ?_).trans
      (pow_le_pow_left₀ (by positivity : 0 ≤ 2*L+1) (by linarith only [hL1]) d)
    intro z hz i
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    exact hrest p hp i
  have halgebra : (L/((3:ℝ)^d*theta))*(3*L)^d = L^(d+1)/theta := by
    rw [mul_pow,pow_succ]
    field_simp
  obtain ⟨z,_,hfiber⟩ := exists_large_real_fiber s Prod.snd hs
    (A := L/((3:ℝ)^d*theta)) (N := (3*L)^d) (by positivity) hprojcount
    (by rw [halgebra]; exact hdense)
  let t := s.filter (fun n => n.2 = z)
  let P := t.image Prod.fst
  have hinj : Set.InjOn Prod.fst (t : Set ((Fin 2 → ℤ) × (Fin d → ℤ))) := by
    intro p hp q hq he
    apply Prod.ext he
    exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
  have hcard : P.card = t.card := Finset.card_image_of_injOn hinj
  apply exists_small_relation_of_dense_strip P (alpha := alpha-F z) (d := v) hrho htheta' hL ha hb
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact hproj q (Finset.mem_filter.mp hq).1
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    have hq' := Finset.mem_filter.mp hq
    have hh := hstrip q hq'.1
    rw [hq'.2] at hh
    have he : a*(q.1 0:ℝ)+b*(q.1 1:ℝ)-(alpha-F z) =
        a*(q.1 0:ℝ)+b*(q.1 1:ℝ)+F z-alpha := by ring
    rw [he]
    exact hh
  · rw [hcard]
    exact hfiber

end WaveTurbulence.Counting
