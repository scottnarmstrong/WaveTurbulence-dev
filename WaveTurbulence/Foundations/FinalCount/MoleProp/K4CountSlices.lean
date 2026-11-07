/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.DotStrip
import Mathlib.Tactic

/-! # Actual coordinate slices for K4 planar fibers

Two retained coordinates and all complementary coordinates reconstruct
the original integer point exactly. The complementary box count has the
literal dimension d−2. No planar counting estimate is assumed here.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

abbrev K4TailIndex {d : ℕ} (i j : Fin d) := {k : Fin d // k ∉ ({i,j} : Finset (Fin d))}

def k4Tail {d : ℕ} (i j : Fin d) (n : Fin d → ℤ) : K4TailIndex i j → ℤ := fun k => n k

def k4Plane {d : ℕ} (i j : Fin d) (n : Fin d → ℤ) : Fin 2 → ℤ := ![n i,n j]

def k4PlaneSlice {d : ℕ} (S : Finset (Fin d → ℤ)) (i j : Fin d)
    (t : K4TailIndex i j → ℤ) : Finset (Fin 2 → ℤ) :=
  (S.filter (fun n => k4Tail i j n=t)).image (k4Plane i j)

/-- The actual two-coordinate projection is injective on each exact tail fiber. -/
theorem k4_plane_injective_on_tail {d : ℕ} (i j : Fin d) (n m : Fin d → ℤ)
    (ht : k4Tail i j n=k4Tail i j m) (hp : k4Plane i j n=k4Plane i j m) : n=m := by
  funext k
  by_cases hi : k=i
  · subst k
    simpa only [k4Plane,Matrix.cons_val_zero] using congrFun hp 0
  by_cases hj : k=j
  · subst k
    simpa only [k4Plane,Matrix.cons_val_one,Matrix.cons_val_zero] using congrFun hp 1
  have hk : k ∉ ({i,j} : Finset (Fin d)) := by simp only [mem_insert,mem_singleton,not_or]; exact ⟨hi,hj⟩
  exact congrFun ht ⟨k,hk⟩

/-- The finite planar image loses no points inside an exact tail fiber. -/
theorem card_k4PlaneSlice {d : ℕ} (S : Finset (Fin d → ℤ)) (i j : Fin d)
    (t : K4TailIndex i j → ℤ) :
    (k4PlaneSlice S i j t).card = (S.filter (fun n => k4Tail i j n=t)).card := by
  apply card_image_of_injOn
  intro n hn m hm hp
  exact k4_plane_injective_on_tail i j n m ((mem_filter.mp hn).2.trans (mem_filter.mp hm).2.symm) hp

/-- The complementary coordinate type has exactly d−2 entries. -/
theorem card_k4TailIndex {d : ℕ} (i j : Fin d) (hij : i ≠ j) :
    Fintype.card (K4TailIndex i j) = d-2 := by
  simp only [K4TailIndex,Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_coe,card_pair hij]

/-- Actual radius-B coordinate boxes yield the required complementary
projection count, uniformly in the arbitrary box center. -/
theorem k4_tail_projection_card_le {d : ℕ} (S : Finset (Fin d → ℤ))
    (i j : Fin d) (hij : i ≠ j) (b : Fin d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hbox : ∀ n ∈ S, ∀ k, |(n k : ℝ)-b k| ≤ B) :
    ((S.image (k4Tail i j)).card : ℝ) ≤ (2*B+1)^(d-2) := by
  classical
  let T := Fintype.piFinset (fun k : K4TailIndex i j => Counting.integerInterval (b k-B) (b k+B))
  have hsub : S.image (k4Tail i j) ⊆ T := by
    intro t ht
    obtain ⟨n,hn,rfl⟩ := mem_image.mp ht
    apply Fintype.mem_piFinset.mpr
    intro k
    apply (Counting.mem_integerInterval _ _ _).mpr
    have hh := abs_le.mp (hbox n hn k)
    change b k-B ≤ (n k : ℝ) ∧ (n k : ℝ) ≤ b k+B
    constructor <;> linarith only [hh.1,hh.2]
  have hc : ((S.image (k4Tail i j)).card : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast card_le_card hsub
  have he : (T.card : ℝ) = ∏ k : K4TailIndex i j,
      ((Counting.integerInterval (b k-B) (b k+B)).card : ℝ) := by
    simp only [T,Fintype.card_piFinset,Nat.cast_prod]
  rw [he] at hc
  have hp : (∏ k : K4TailIndex i j, ((Counting.integerInterval (b k-B) (b k+B)).card : ℝ)) ≤
      ∏ _k : K4TailIndex i j, (2*B+1) :=
    prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun k _ => Counting.card_integerInterval_le (b k) hB)
  apply hc.trans
  simpa only [prod_const,card_univ,card_k4TailIndex i j hij] using hp

/-- A literal finite-coordinate partition into two selected entries and
their complement; used for both momentum strips and squared radii. -/
theorem k4_coordinate_sum_split {d : ℕ} (i j : Fin d) (hij : i ≠ j) (f : Fin d → ℝ) :
    ∑ k, f k = f i+f j+∑ k : K4TailIndex i j, f k := by
  have hdecomp := sum_filter_add_sum_filter_not (univ : Finset (Fin d))
    (fun k => k ∈ ({i,j} : Finset (Fin d))) f
  have he : univ.filter (fun k => k ∈ ({i,j} : Finset (Fin d))) = {i,j} := by ext k; simp
  rw [he,sum_pair hij] at hdecomp
  rw [Finset.sum_subtype (p := fun k => k ∉ ({i,j} : Finset (Fin d)))
    (univ.filter (fun k => k ∉ ({i,j} : Finset (Fin d)))) (by intro k; simp) f] at hdecomp
  exact hdecomp.symm

/-- The squared radius splits exactly into the retained plane and the
fixed complementary coordinates. -/
theorem k4_plane_norm_sq {d : ℕ} (i j : Fin d) (hij : i ≠ j) (n : Fin d → ℤ) :
    ‖latticePoint 1 n‖^2 = ‖latticePoint 1 (k4Plane i j n)‖^2+
      ∑ k : K4TailIndex i j, (n k : ℝ)^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,latticePoint,div_one,Fin.sum_univ_two,k4Plane,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  exact k4_coordinate_sum_split i j hij (fun k => (n k : ℝ)^2)

/-- The actual linear strip has a fixed complementary contribution inside
each tail fiber. -/
theorem k4_plane_inner {d : ℕ} (i j : Fin d) (hij : i ≠ j)
    (r : Mom d) (n : Fin d → ℤ) :
    inner ℝ r (latticePoint 1 n) =
      inner ℝ (WithLp.toLp 2 ![r i,r j] : Mom 2) (latticePoint 1 (k4Plane i j n))+
      ∑ k : K4TailIndex i j, r k*(n k : ℝ) := by
  simp only [PiLp.inner_apply,Real.inner_apply,latticePoint,div_one,Fin.sum_univ_two,k4Plane,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  exact k4_coordinate_sum_split i j hij (fun k => r k*(n k : ℝ))

end WaveTurbulence.MoleProp
