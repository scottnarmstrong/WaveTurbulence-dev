/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SlotBounds
/-! Every mixed slot in the actual Duhamel identity is integrable for a Z remainder. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Set
open SysAPI

/-- The analytic side conditions of the Duhamel identity follow from the existing Z class. -/
theorem intervalIntegrable_slotTriple {d p : ℕ} (L γ δ : ℝ) (hL : 0 < L)
    (Ntr : ℕ) {c : (Fin d → ℤ) → ℂ} (hc : Summable fun n => ‖c n‖)
    {Λ : ℝ} {b : ZTime p → (Fin d → ℤ) → ℂ}
    (hb : b ∈ ZSpace L Λ p) (hΛ : (d : ℝ) + 1 ≤ Λ)
    (x : Slot Ntr × Slot Ntr × Slot Ntr) (t : ℝ) (n : Fin d → ℤ) :
    IntervalIntegrable (fun s => aNonlin L γ δ 1 s (slotVal L γ δ p Ntr c b x.1 s)
      (fun k => (starRingEnd ℂ) (slotVal L γ δ p Ntr c b x.2.1 s k))
      (slotVal L γ δ p Ntr c b x.2.2 s) n) volume p t := by
  have hbs := zSpace_summable hL hb hΛ
  have hmeas (o : Slot Ntr) (k : Fin d → ℤ) :
      StronglyMeasurable fun s => slotVal L γ δ p Ntr c b o s k := by
    cases o with
    | none => exact (continuous_zExtend hb k).stronglyMeasurable
    | some N => exact stronglyMeasurable_treeTermN L γ δ p N hc k
  have hsum (o : Slot Ntr) (s : ℝ) : Summable fun k => ‖slotVal L γ δ p Ntr c b o s k‖ :=
    summable_slotVal L γ δ p Ntr hc hbs o s
  have hbound (o : Slot Ntr) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s ≤ max (p : ℝ) t,
      (∑' k, ‖slotVal L γ δ p Ntr c b o s k‖) ≤ C := by
    cases o with
    | none =>
      obtain ⟨C, hC0, hC⟩ := exists_tsum_zExtend_bound hL hb hΛ
      exact ⟨C, hC0, fun s _ => hC s⟩
    | some N => exact exists_tsum_treeTermN_bound L γ δ p N (max (p : ℝ) t) hc
  choose C hC0 hC using hbound
  have hsm := stronglyMeasurable_aNonlin L γ δ (hmeas x.1) (hmeas x.2.1) (hmeas x.2.2)
    (hsum x.1) (hsum x.2.1) (hsum x.2.2) n
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded
    (M := ‖((δ / (2 * L ^ ((d : ℝ) - γ)) : ℝ) : ℂ) * (Complex.I * ((1 : ℤ) : ℂ))‖ *
      (C x.1 * C x.2.1 * C x.2.2))
    (by rw [Set.uIoc]; exact measure_Ioc_lt_top.ne) hsm.aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_uIoc fun s hs => ?_)
  have hst : s ≤ max (p : ℝ) t := hs.2
  refine (norm_aNonlin_le_tsum L γ δ 1 s (hsum x.1 s)
    (by simpa using hsum x.2.1 s) (hsum x.2.2 s) n).trans
    (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  simp only [Complex.norm_conj]
  exact mul_le_mul
    (mul_le_mul (hC x.1 s hst) (hC x.2.1 s hst) (tsum_nonneg fun _ => norm_nonneg _) (hC0 _))
    (hC x.2.2 s hst) (tsum_nonneg fun _ => norm_nonneg _)
    (mul_nonneg (hC0 _) (hC0 _))

end WaveTurbulence.Induct
