/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.CountLemmas.A23HalfShell
public import WaveTurbulence.Foundations.CountLemmas.CoupledSets
public import WaveTurbulence.Foundations.CountLemmas.DotStrip
public import WaveTurbulence.Foundations.CountLemmas.BroadBand
public import WaveTurbulence.Foundations.WeylSums.ThreeVectorReduction

/-!
# The anti-parallel form `ζ = x − v`: fibers, the per-vector strip bound, the bilinear sums

For the selector `ζ = x − v` of `coupledTripleSet`, the two constraints decouple once `x` is fixed:
`#S = ∑_x N_y(x) N_z(x)` (`ncard_coupledTripleSet_zero_eq_sum`), with

* `N_y(X) = #{Y near b : |⟨x, y⟩ − α| ≤ τ}`, `N_z(X) = #{Z near c : |⟨x − v, z⟩ − β| ≤ τ}`;
* (P) `N_y(X) ≤ (2L+1)^{d-1} (2τL²/|X|_∞ + 1)` for `X ≠ 0`, and the same for `N_z` with `X − V`
  (`card_ysF_le`, `card_zsF_le`; referee §4.3, "(P)");
* (Bi) `∑_x N_y(x), ∑_x N_z(x) ≤ C τ L^{2d}` (`sum_card_ysF_le`, `sum_card_zsF_le`; the landed broad bilinear band).
-/

public section

open Finset Set

namespace WaveTurbulence.CountLemmas

variable {d : ℕ}

open Classical in
/-- The lattice points near `a` as a finset. -/
@[expose] noncomputable def nearFinset (L : ℝ) (a : Mom d) : Finset (Fin d → ℤ) :=
  (Counting.latticeBox (fun i => L * a i) L).filter (NearLattice L a)

theorem mem_nearFinset {L : ℝ} (hL : 0 < L) (a : Mom d) (n : Fin d → ℤ) :
    n ∈ nearFinset L a ↔ NearLattice L a n := by
  classical
  simp only [nearFinset, Finset.mem_filter, and_iff_right_iff_imp]
  exact fun h => nearLattice_mem_box hL a n h

theorem card_nearFinset_le {L : ℝ} (hL : 0 < L) (a : Mom d) :
    ((nearFinset L a).card : ℝ) ≤ (2 * L + 1) ^ d := by
  classical
  have h : (nearFinset L a).card ≤ (Counting.latticeBox (fun i => L * a i) L).card := by
    unfold nearFinset
    convert Finset.card_filter_le _ _
  exact (by exact_mod_cast h : ((nearFinset L a).card : ℝ) ≤
    (Counting.latticeBox (fun i => L * a i) L).card).trans (Counting.card_latticeBox_le _ hL.le)

open Classical in
/-- The `y`-fiber of `x`. -/
@[expose] noncomputable def ysF (L : ℝ) (b : Mom d) (α τ : ℝ) (X : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  (nearFinset L b).filter fun Y => |inner ℝ (latticePoint L X) (latticePoint L Y) - α| ≤ τ

open Classical in
/-- The `z`-fiber of `x` for `ζ = x − v`. -/
@[expose] noncomputable def zsF (L : ℝ) (c v : Mom d) (β τ : ℝ) (X : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  (nearFinset L c).filter fun Z => |inner ℝ (latticePoint L X - v) (latticePoint L Z) - β| ≤ τ

/-- **Fiber decomposition** `#S = ∑_x N_y(x) N_z(x)` for `ζ = x − v`. -/
theorem ncard_coupledTripleSet_zero_eq_sum {L : ℝ} (hL : 0 < L) (a b c v : Mom d) (α β τ : ℝ) :
    ((coupledTripleSet L a b c v α β τ 0).ncard : ℝ) =
      ∑ X ∈ nearFinset L a, ((ysF L b α τ X).card : ℝ) * (zsF L c v β τ X).card := by
  classical
  have hS : coupledTripleSet L a b c v α β τ 0 =
      ((nearFinset L a ×ˢ (nearFinset L b ×ˢ nearFinset L c)).filter fun q =>
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2.1) - α| ≤ τ ∧
        |inner ℝ (latticePoint L q.1 - v) (latticePoint L q.2.2) - β| ≤ τ : Set _) := by
    ext q
    simp only [coupledTripleSet, Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_product,
      mem_nearFinset hL, Matrix.cons_val_zero]
    tauto
  rw [hS, Set.ncard_coe_finset]
  have hprod : ∀ X : Fin d → ℤ, ((nearFinset L b ×ˢ nearFinset L c).filter fun p : (Fin d → ℤ) × (Fin d → ℤ) =>
      |inner ℝ (latticePoint L X) (latticePoint L p.1) - α| ≤ τ ∧
      |inner ℝ (latticePoint L X - v) (latticePoint L p.2) - β| ≤ τ) = ysF L b α τ X ×ˢ zsF L c v β τ X := by
    intro X
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, ysF, zsF]
    tauto
  have key : ((nearFinset L a ×ˢ (nearFinset L b ×ˢ nearFinset L c)).filter fun q =>
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2.1) - α| ≤ τ ∧
        |inner ℝ (latticePoint L q.1 - v) (latticePoint L q.2.2) - β| ≤ τ).card =
      ∑ X ∈ nearFinset L a, (ysF L b α τ X).card * (zsF L c v β τ X).card := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun X _ => ?_
    have h := congrArg Finset.card (hprod X)
    rw [Finset.card_filter, Finset.card_product] at h
    exact h
  rw [key]
  push_cast
  rfl

theorem latticePoint_coord_abs {L : ℝ} (hL : 0 < L) (X : Fin d → ℤ) (i : Fin d) :
    |latticePoint L X i| = |(X i : ℝ)| / L := by
  simp [latticePoint, abs_div, abs_of_pos hL]

/-- **(P) for the `y`-fiber**: `N_y(X) ≤ (2L+1)^{d-1} (2τL²/|X|_∞ + 1)` for `X ≠ 0`. -/
theorem card_ysF_le {L : ℝ} (hd : 0 < d) (hL : 0 < L) {τ : ℝ} (hτ : 0 ≤ τ) (b : Mom d) (α : ℝ)
    {X : Fin d → ℤ} (hX : X ≠ 0) :
    ((ysF L b α τ X).card : ℝ) ≤ (2 * L + 1) ^ (d - 1) * (2 * τ * L ^ 2 / supNat X + 1) := by
  classical
  obtain ⟨i, hi⟩ := exists_coord_eq_supNat hd X
  have hpos : 0 < supNat X := Nat.pos_of_ne_zero ((supNat_eq_zero_iff X).not.mpr hX)
  have hXi : (X i : ℝ) ≠ 0 := by
    have : (X i).natAbs ≠ 0 := by omega
    exact_mod_cast Int.natAbs_ne_zero.mp this
  have hri : latticePoint L X i ≠ 0 := by
    simp only [latticePoint]
    exact div_ne_zero hXi hL.ne'
  have hc := card_dot_strip_ball_le (ysF L b α τ X) hL zero_le_one hτ b (latticePoint L X) α i hri
    (fun n hn => (mem_nearFinset hL b n).mp (Finset.mem_filter.mp hn).1)
    (fun n hn => (Finset.mem_filter.mp hn).2)
  have habs : |latticePoint L X i| = supNat X / L := by
    rw [latticePoint_coord_abs hL, ← hi, ← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [habs, mul_one] at hc
  have heq : 2 * τ * L / (supNat X / L) = 2 * τ * L ^ 2 / supNat X := by
    field_simp
  rwa [heq] at hc

/-- **(P) for the `z`-fiber**: `N_z(X) ≤ (2L+1)^{d-1} (2τL²/|X − V|_∞ + 1)` for `X ≠ V`. -/
theorem card_zsF_le {L : ℝ} (hd : 0 < d) (hL : 0 < L) {τ : ℝ} (hτ : 0 ≤ τ) (c : Mom d) (nv : Fin d → ℤ)
    (β : ℝ) {X : Fin d → ℤ} (hX : X ≠ nv) :
    ((zsF L c (latticePoint L nv) β τ X).card : ℝ) ≤
      (2 * L + 1) ^ (d - 1) * (2 * τ * L ^ 2 / supNat (X - nv) + 1) := by
  classical
  have hX' : X - nv ≠ 0 := sub_ne_zero.mpr hX
  have he : ∀ Z, inner ℝ (latticePoint L X - latticePoint L nv) (latticePoint L Z) =
      inner ℝ (latticePoint L (X - nv)) (latticePoint L Z) := fun Z => by
    rw [WeylSums.latticePoint_sub_eq]
  have hset : zsF L c (latticePoint L nv) β τ X = ysF L c β τ (X - nv) := by
    ext Z
    simp only [zsF, ysF, Finset.mem_filter, he]
  rw [hset]
  exact card_ysF_le hd hL hτ c β hX'

/-- **(Bi)**: `∑_x N_y(x) ≤ C τ L^{2d}`. -/
theorem sum_card_ysF_le (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ L τ : ℝ, 2 ≤ L → 0 < τ → 1 / τ ≤ L ^ 2 → ∀ a b : Mom d, ∀ α : ℝ,
      ∑ X ∈ nearFinset L a, ((ysF L b α τ X).card : ℝ) ≤ C * τ * L ^ (2 * (d : ℝ)) := by
  classical
  obtain ⟨C, hC, hband⟩ := exists_broad_bilinear_band_bound d hd
  refine ⟨C, hC, fun L τ hL hτ hwin a b α => ?_⟩
  have hLp : 0 < L := by linarith
  let s := (nearFinset L a).sigma fun X => ysF L b α τ X
  have hcard : ∑ X ∈ nearFinset L a, ((ysF L b α τ X).card : ℝ) = (s.card : ℝ) := by
    rw [Finset.card_sigma]; push_cast; rfl
  rw [hcard]
  have hinj : Set.InjOn (fun p : (_ : Fin d → ℤ) × (Fin d → ℤ) => (p.1, p.2)) (s : Set _) := by
    intro p _ q _ h
    simp only [Prod.mk.injEq] at h
    exact Sigma.ext h.1 (heq_of_eq h.2)
  rw [← Finset.card_image_of_injOn hinj]
  apply hband L τ hL hτ hwin a b α
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hX, hY⟩ := Finset.mem_sigma.mp hp
  have hYm := Finset.mem_filter.mp hY
  exact ⟨((mem_nearFinset hLp a _).mp hX).trans (by norm_num),
    ((mem_nearFinset hLp b _).mp hYm.1).trans (by norm_num), hYm.2⟩

/-- **(Bi) for the `z`-fibers**: `∑_x N_z(x) ≤ C τ L^{2d}`. -/
theorem sum_card_zsF_le (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ L τ : ℝ, 2 ≤ L → 0 < τ → 1 / τ ≤ L ^ 2 → ∀ a c : Mom d, ∀ nv : Fin d → ℤ, ∀ β : ℝ,
      ∑ X ∈ nearFinset L a, ((zsF L c (latticePoint L nv) β τ X).card : ℝ) ≤ C * τ * L ^ (2 * (d : ℝ)) := by
  classical
  obtain ⟨C, hC, hband⟩ := exists_broad_bilinear_band_bound d hd
  refine ⟨C, hC, fun L τ hL hτ hwin a c nv β => ?_⟩
  have hLp : 0 < L := by linarith
  let s := (nearFinset L a).sigma fun X => zsF L c (latticePoint L nv) β τ X
  have hcard : ∑ X ∈ nearFinset L a, ((zsF L c (latticePoint L nv) β τ X).card : ℝ) = (s.card : ℝ) := by
    rw [Finset.card_sigma]; push_cast; rfl
  rw [hcard]
  have hinj : Set.InjOn (fun p : (_ : Fin d → ℤ) × (Fin d → ℤ) => (p.1 - nv, p.2)) (s : Set _) := by
    intro p _ q _ h
    simp only [Prod.mk.injEq, sub_left_inj] at h
    exact Sigma.ext h.1 (heq_of_eq h.2)
  rw [← Finset.card_image_of_injOn hinj]
  apply hband L τ hL hτ hwin (a - latticePoint L nv) c β
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hX, hZ⟩ := Finset.mem_sigma.mp hp
  have hZm := Finset.mem_filter.mp hZ
  have hX1 := (mem_nearFinset hLp a _).mp hX
  refine ⟨?_, ((mem_nearFinset hLp c _).mp hZm.1).trans (by norm_num), ?_⟩
  · rw [WeylSums.latticePoint_sub_eq]
    have : latticePoint L p.1 - latticePoint L nv - (a - latticePoint L nv) = latticePoint L p.1 - a := by abel
    rw [this]
    exact hX1.trans (by norm_num)
  · rw [WeylSums.latticePoint_sub_eq]
    exact hZm.2

end WaveTurbulence.CountLemmas
