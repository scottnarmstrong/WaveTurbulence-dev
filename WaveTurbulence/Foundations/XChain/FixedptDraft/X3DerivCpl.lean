/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.ISlotIntegrability
public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3KernelNorm
public import WaveTurbulence.Foundations.XChain.FlowerDraft.X2Couple

/-!
# X3: `∂_t a^tr` and `∂_t ℒ₀` (T L2312)

- `aTr_sub`: `a^tr(t) − a^tr(t₀) = ∫_{t₀}^t ∂_t a^tr`. It follows tree by tree from the Duhamel identity O-TR1
  (`treeTerm_node`).
- `L0_eq`: `ℒ₀(t) = ∫_p^t ∂_t ℒ₀`. The slots of `ℒ₀` contain no `b`, so `Lop_eq_sum` gives it with INDUCT's slot
  integrability.

Here `∂_t a^tr = aTrDt` and `∂_t ℒ₀ = L0Dt` are the Duhamel integrands of X2's couple layer. These identities let Part 1
control `sup_t` through Sobolev in `t` (T (sobolev)).
-/

@[expose] public section

open WaveTurbulence.X2E
namespace WaveTurbulence.Fixedpt

open MeasureTheory Set

variable (L γ δ : ℝ) {d : ℕ}

theorem treeTerm_sub (p : ℕ) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun k => ‖b k‖) (T : TTree) {t t₀ : ℝ}
    (ht : (p : ℝ) ≤ t) (ht₀ : (p : ℝ) ≤ t₀) (n : Fin d → ℤ) :
    treeTerm L γ δ p T b t n - treeTerm L γ δ p T b t₀ n = ∫ s in t₀..t, treeTermDt L γ δ p T b s n := by
  cases T with
  | leaf => simp [SysAPI.treeTerm_leaf, treeTermDt]
  | node l m r =>
    rw [SysAPI.treeTerm_node l m r L γ δ p hb ht, SysAPI.treeTerm_node l m r L γ δ p hb ht₀,
      intervalIntegral.integral_interval_sub_left (SysAPI.intervalIntegrable_treeTriple L γ δ p l m r hb t n)
        (SysAPI.intervalIntegrable_treeTriple L γ δ p l m r hb t₀ n)]
    rfl

theorem intervalIntegrable_treeTermDt (p : ℕ) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun k => ‖b k‖) (T : TTree)
    (t₀ t : ℝ) (n : Fin d → ℤ) : IntervalIntegrable (fun s => treeTermDt L γ δ p T b s n) volume t₀ t := by
  cases T with
  | leaf => simp [treeTermDt]
  | node l m r =>
    exact (SysAPI.intervalIntegrable_treeTriple L γ δ p l m r hb t₀ n).symm.trans
      (SysAPI.intervalIntegrable_treeTriple L γ δ p l m r hb t n)

theorem aTrDt_eq_sum (p Ntr : ℕ) (b : (Fin d → ℤ) → ℂ) (s : ℝ) (n : Fin d → ℤ) :
    aTrDt L γ δ p Ntr b s n =
      ∑ N ∈ Finset.range (Ntr + 1), ∑ T ∈ SysAPI.treesOfOrder N, treeTermDt L γ δ p T b s n := by
  unfold aTrDt
  refine Finset.sum_congr rfl fun N _ => ?_
  unfold SysAPI.treesOfOrder
  rw [← finsum_mem_eq_finite_toFinset_sum _ (SysAPI.finite_order_eq N)]
  rfl

/-- **`a^tr(t) − a^tr(t₀) = ∫_{t₀}^t ∂_t a^tr`.** -/
theorem aTr_sub (p Ntr : ℕ) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun k => ‖b k‖) {t t₀ : ℝ}
    (ht : (p : ℝ) ≤ t) (ht₀ : (p : ℝ) ≤ t₀) (n : Fin d → ℤ) :
    aTr L γ δ p Ntr b t n - aTr L γ δ p Ntr b t₀ n = ∫ s in t₀..t, aTrDt L γ δ p Ntr b s n := by
  simp only [aTrDt_eq_sum]
  have hI : ∀ N ∈ Finset.range (Ntr + 1), IntervalIntegrable
      (fun s => ∑ T ∈ SysAPI.treesOfOrder N, treeTermDt L γ δ p T b s n) volume t₀ t := fun N _ => by
    have h := IntervalIntegrable.sum (SysAPI.treesOfOrder N)
      (fun T _ => intervalIntegrable_treeTermDt L γ δ p hb T t₀ t n)
    convert h using 1
    funext s
    simp [Finset.sum_apply]
  rw [intervalIntegral.integral_finsetSum
    (f := fun N s => ∑ T ∈ SysAPI.treesOfOrder N, treeTermDt L γ δ p T b s n) hI]
  unfold aTr
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [SysAPI.treeTermN_eq_sum, SysAPI.treeTermN_eq_sum, ← Finset.sum_sub_distrib,
    intervalIntegral.integral_finsetSum (f := fun T s => treeTermDt L γ δ p T b s n)
      fun T _ => intervalIntegrable_treeTermDt L γ δ p hb T t₀ t n]
  exact Finset.sum_congr rfl fun T _ => treeTerm_sub L γ δ p hb T ht ht₀ n

theorem slotVal_eq_slotValAt (p Ntr : ℕ) (aP : (Fin d → ℤ) → ℂ) (b : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ)
    {o : Slot Ntr} (ho : o ≠ none) (s : ℝ) :
    SysAPI.slotVal L γ δ p Ntr aP b o s = slotValAt L γ δ p Ntr aP o s := by
  cases o with
  | none => exact absurd rfl ho
  | some N => rfl

theorem slots_ne_none {Ntr : ℕ} {x : Slot Ntr × Slot Ntr × Slot Ntr} (h : slotCountB x = 0) :
    x.1 ≠ none ∧ x.2.1 ≠ none ∧ x.2.2 ≠ none := by
  unfold slotCountB at h
  refine ⟨fun h1 => ?_, fun h1 => ?_, fun h1 => ?_⟩ <;>
  · have := List.count_pos_iff.2 (by simp [h1] : (none : Slot Ntr) ∈ [x.1, x.2.1, x.2.2])
    omega

/-- **`ℒ₀(t) = ∫_p^t ∂_t ℒ₀`.** -/
theorem L0_eq (hL : 0 < L) (p Ntr : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖)
    (b₀ : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ) :
    Lop L γ δ p Ntr aP 0 b₀ t n = ∫ s in (p : ℝ)..t, L0Dt L γ δ p Ntr aP s n := by
  rw [SysAPI.Lop_eq_sum]
  unfold L0Dt
  have hzero : (0 : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ) ∈ ZSpace L ((d : ℝ) + 1) p := by
    refine ⟨fun _ => continuous_const, ?_⟩
    rw [show (0 : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ) = 0 from rfl]
    have := ZNorm_zero (d := d) (p := p) (L := L) (Λ := (d : ℝ) + 1)
    rw [this]
    exact ENNReal.zero_lt_top
  have hrw : ∀ (b : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ),
      ∀ x ∈ (Finset.univ : Finset (Slot Ntr × Slot Ntr × Slot Ntr)).filter
        (fun x => slotCountB x = 0 ∧ (0 = 0 → Ntr ≤ slotOrder x)), ∀ s,
      aNonlin L γ δ 1 s (SysAPI.slotVal L γ δ p Ntr aP b x.1 s)
        (fun m => (starRingEnd ℂ) (SysAPI.slotVal L γ δ p Ntr aP b x.2.1 s m))
        (SysAPI.slotVal L γ δ p Ntr aP b x.2.2 s) n =
      aNonlin L γ δ 1 s (slotValAt L γ δ p Ntr aP x.1 s)
        (fun m => (starRingEnd ℂ) (slotValAt L γ δ p Ntr aP x.2.1 s m)) (slotValAt L γ δ p Ntr aP x.2.2 s) n := by
    intro b x hx s
    obtain ⟨h1, h2, h3⟩ := slots_ne_none (Finset.mem_filter.1 hx).2.1
    rw [slotVal_eq_slotValAt L γ δ p Ntr aP b h1, slotVal_eq_slotValAt L γ δ p Ntr aP b h2,
      slotVal_eq_slotValAt L γ δ p Ntr aP b h3]
  rw [intervalIntegral.integral_finsetSum (f := fun (x : Slot Ntr × Slot Ntr × Slot Ntr) (s : ℝ) =>
      aNonlin L γ δ 1 s (slotValAt L γ δ p Ntr aP x.1 s)
      (fun m => (starRingEnd ℂ) (slotValAt L γ δ p Ntr aP x.2.1 s m)) (slotValAt L γ δ p Ntr aP x.2.2 s) n)
    fun x hx => by
      have h := intervalIntegrable_slotTriple L γ δ hL Ntr haP hzero (by linarith) x t n
      rwa [funext (hrw 0 x hx)] at h]
  exact Finset.sum_congr rfl fun x hx => intervalIntegral.integral_congr fun s _ => hrw b₀ x hx s

end WaveTurbulence.Fixedpt
