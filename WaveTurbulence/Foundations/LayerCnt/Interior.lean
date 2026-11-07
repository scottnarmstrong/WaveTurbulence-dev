/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.BondExp
public import WaveTurbulence.Foundations.LayerCnt.LadderIncidences
import Mathlib.Tactic

/-! # Dart sums over the interior atoms of a rung sequence (TARGET layerlad)

For a `FullRungSequence` (rungs `1 ≤ i ≤ n`, every interior atom with exactly four incidences) the
dart sum of `|f a − f nbr|` over the interior atoms is `4 Σ|A_i − B_i|` plus the rail variations from
both sides.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open Finset WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

theorem sum_dartsAt_of_four (hM : M.IsMolecule) {x : V} {ns : Fin 4 → V} (R : FourIncidences M x ns)
    (F : V → ℕ) : ∑ d ∈ M.dartsAt x, F (M.atom (M.mate d)) = ∑ j : Fin 4, F (ns j) := by
  rw [← fourIncidences_image M hM R, Finset.sum_image (fun i _ j _ h => R.injective h)]
  apply Finset.sum_congr rfl
  intro j _; rw [R.neighbor_eq]

/-- Interior atoms of a rung sequence with rungs `1..n`. -/
@[expose] def intAtoms (u v : ℕ → V) (n : ℕ) : Finset V :=
  (Ico 1 (n + 1)).image u ∪ (Ico 1 (n + 1)).image v

theorem intAtoms_disjoint {n : ℕ} (R : FullRungSequence M n) :
    Disjoint ((Ico 1 (n + 1)).image R.u) ((Ico 1 (n + 1)).image R.v) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [mem_image, mem_Ico] at ha hb
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨j, hj, hij⟩ := hb
  have := @R.distinct (Sum.inl ⟨i - 1, by omega⟩) (Sum.inr ⟨j - 1, by omega⟩)
    (by simp only [Sum.elim_inl, Sum.elim_inr]; rw [show i - 1 + 1 = i by omega, show j - 1 + 1 = j by omega]; exact hij.symm)
  simp at this

theorem u_injOn {n : ℕ} (R : FullRungSequence M n) : Set.InjOn R.u (Ico 1 (n + 1) : Finset ℕ) := by
  intro i hi j hj h
  simp only [Finset.coe_Ico, Set.mem_Ico] at hi hj
  have := @R.distinct (Sum.inl ⟨i - 1, by omega⟩) (Sum.inl ⟨j - 1, by omega⟩)
    (by simp only [Sum.elim_inl]; rw [show i - 1 + 1 = i by omega, show j - 1 + 1 = j by omega]; exact h)
  simp at this; omega

theorem v_injOn {n : ℕ} (R : FullRungSequence M n) : Set.InjOn R.v (Ico 1 (n + 1) : Finset ℕ) := by
  intro i hi j hj h
  simp only [Finset.coe_Ico, Set.mem_Ico] at hi hj
  have := @R.distinct (Sum.inr ⟨i - 1, by omega⟩) (Sum.inr ⟨j - 1, by omega⟩)
    (by simp only [Sum.elim_inr]; rw [show i - 1 + 1 = i by omega, show j - 1 + 1 = j by omega]; exact h)
  simp at this; omega

/-- The exact dart sum over the interior atoms. -/
theorem interior_dartSum (hM : M.IsMolecule) {n : ℕ} (R : FullRungSequence M n) (f : V → ℕ) :
    ∑ a ∈ intAtoms R.u R.v n, ∑ x ∈ M.dartsAt a, dst (f a) (f (M.atom (M.mate x))) =
      ∑ i ∈ Ico 1 (n + 1), (4 * dst (f (R.u i)) (f (R.v i)) +
        dst (f (R.u i)) (f (R.u (i - 1))) + dst (f (R.u i)) (f (R.u (i + 1))) +
        dst (f (R.v i)) (f (R.v (i - 1))) + dst (f (R.v i)) (f (R.v (i + 1)))) := by
  unfold intAtoms
  rw [Finset.sum_union (intAtoms_disjoint M R), Finset.sum_image (u_injOn M R),
    Finset.sum_image (v_injOn M R), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mem_Ico] at hi
  have hu := (R.upper i hi.1 (by omega))
  have hv := (R.lower i hi.1 (by omega))
  rw [sum_dartsAt_of_four M hM hu (fun y => dst (f (R.u i)) (f y)),
    sum_dartsAt_of_four M hM hv (fun y => dst (f (R.v i)) (f y))]
  simp [Fin.sum_univ_four]
  rw [dst_comm (f (R.v i)) (f (R.u i))]
  ring

end WaveTurbulence.LayerCnt

namespace WaveTurbulence.LayerCnt
open Finset WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

theorem sum_pred_eq_tvF (a : ℕ → ℕ) (n : ℕ) :
    ∑ i ∈ Ico 1 (n + 1), dst (a i) (a (i - 1)) = tvF a 0 n := by
  unfold tvF
  have := Finset.sum_Ico_add' (fun i => dst (a i) (a (i - 1))) 0 n 1
  simp only [Nat.zero_add] at this
  rw [← this]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.add_sub_cancel]
  exact dst_comm _ _

theorem tvF_zero_le {a : ℕ → ℕ} {𝔇 : ℕ} (hb : ∀ i, a i ≤ 𝔇) (n : ℕ) :
    tvF a 0 n ≤ tvF a 1 n + 𝔇 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tvF]
  · unfold tvF
    rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) hn]
    have : ∑ i ∈ Ico 0 1, dst (a i) (a (i + 1)) ≤ 𝔇 := by
      simp only [Nat.Ico_zero_eq_range, Finset.range_one, Finset.sum_singleton]
      exact dst_le (hb _) (hb _)
    omega

theorem tvF_succ_le {a : ℕ → ℕ} {𝔇 : ℕ} (hb : ∀ i, a i ≤ 𝔇) (n : ℕ) :
    tvF a 1 (n + 1) ≤ tvF a 1 n + 𝔇 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tvF]
  · unfold tvF
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n)]
    have := dst_le (hb n) (hb (n + 1))
    omega

theorem sum_dst_le_incCnt {A B : ℕ → ℕ} {𝔇 : ℕ} (hA : ∀ i, A i ≤ 𝔇) (hB : ∀ i, B i ≤ 𝔇) (n : ℕ) :
    ∑ i ∈ Ico 1 (n + 1), dst (A i) (B i) ≤ 𝔇 * incCnt A B 1 n := by
  unfold incCnt
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases h : A i = B i
  · simp [h, dst]
  · simp only [h, ite_false, mul_one]; exact dst_le (hA i) (hB i)

theorem tvab_eq (a b : ℕ → ℕ) (s e : ℕ) : tvab a b s e = tvF a s e + tvF b s e := by
  unfold tvab tvF; rw [Finset.sum_add_distrib]

/-- The interior dart sum is bounded by the rung incoherence and the interior rail variation.
Here `A i = f (u i)` and `B i = f (v i)` are the two rung layers. -/
theorem interior_dartSum_le (hM : M.IsMolecule) {n : ℕ} (R : FullRungSequence M n) {f : V → ℕ} {𝔇 : ℕ}
    (hf : ∀ x, f x ≤ 𝔇) (A B : ℕ → ℕ) (hA : ∀ i, A i = f (R.u i)) (hB : ∀ i, B i = f (R.v i)) :
    ∑ a ∈ intAtoms R.u R.v n, ∑ x ∈ M.dartsAt a, dst (f a) (f (M.atom (M.mate x))) ≤
      4 * (𝔇 * incCnt A B 1 n) + 2 * tvab A B 1 n + 4 * 𝔇 := by
  rw [interior_dartSum M hM R f]
  have hAb : ∀ i, A i ≤ 𝔇 := fun i => (hA i) ▸ hf _
  have hBb : ∀ i, B i ≤ 𝔇 := fun i => (hB i) ▸ hf _
  have e : ∑ i ∈ Ico 1 (n + 1), (4 * dst (f (R.u i)) (f (R.v i)) +
        dst (f (R.u i)) (f (R.u (i - 1))) + dst (f (R.u i)) (f (R.u (i + 1))) +
        dst (f (R.v i)) (f (R.v (i - 1))) + dst (f (R.v i)) (f (R.v (i + 1)))) =
      4 * ∑ i ∈ Ico 1 (n + 1), dst (A i) (B i) + (tvF A 0 n + tvF B 0 n) + (tvF A 1 (n + 1) + tvF B 1 (n + 1)) := by
    rw [Finset.mul_sum, ← sum_pred_eq_tvF, ← sum_pred_eq_tvF]
    have : ∀ a : ℕ → ℕ, tvF a 1 (n + 1) = ∑ i ∈ Ico 1 (n + 1), dst (a i) (a (i + 1)) := fun a => rfl
    rw [this, this]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [hA i, hB i, hA (i - 1), hB (i - 1), hA (i + 1), hB (i + 1)]; ring
  rw [e, tvab_eq]
  have h1 := sum_dst_le_incCnt hAb hBb n
  have h2 := tvF_zero_le hAb n
  have h3 := tvF_zero_le hBb n
  have h4 := tvF_succ_le hAb n
  have h5 := tvF_succ_le hBb n
  omega

end WaveTurbulence.LayerCnt
