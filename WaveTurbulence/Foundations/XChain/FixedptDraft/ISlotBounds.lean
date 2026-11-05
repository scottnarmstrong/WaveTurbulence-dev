/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.FixedptDraft.IZBounds
public import WaveTurbulence.Foundations.XChain.FixedptDraft.ITreeTimeContinuity
/-! (Copied verbatim from wt-cumul's INDUCT `SlotBounds.lean`, sha256 `26fd8373a4613c78e79077b8125de77aa602a5d9e7dd7d93e67e89484ef52002`; namespace `Induct` ↦ `Fixedpt` and the
imports of copied INDUCT modules renamed.)

 Uniform bounds and measurability for every Duhamel slot, including the Z remainder. -/
public section
namespace WaveTurbulence.Fixedpt
open MeasureTheory Finset Set
open SysAPI

theorem stronglyMeasurable_treeTermN {d : ℕ} (L γ δ : ℝ) (p N : ℕ)
    {c : (Fin d → ℤ) → ℂ} (hc : Summable fun n => ‖c n‖) (n : Fin d → ℤ) :
    StronglyMeasurable fun t => treeTermN L γ δ p N c t n := by
  simp only [treeTermN_eq_sum]
  exact Finset.stronglyMeasurable_fun_sum _ fun S _ => stronglyMeasurable_treeTerm L γ δ p S hc n

/-- Absolute lattice sums of each order have a uniform bound on bounded forward time sets. -/
theorem exists_tsum_treeTermN_bound {d : ℕ} (L γ δ : ℝ) (p N : ℕ) (T : ℝ)
    {c : (Fin d → ℤ) → ℂ} (hc : Summable fun n => ‖c n‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ≤ T, (∑' n, ‖treeTermN L γ δ p N c t n‖) ≤ C := by
  classical
  let B := fun S => ‖treePrefactor L γ δ d S‖ * (boxVol S p T *
    ∑' z : GLeaf (single S) → (Fin d → ℤ), ∏ ℓ : GLeaf (single S), ‖c (z ℓ)‖)
  have hB (S : TTree) : 0 ≤ B S :=
    mul_nonneg (norm_nonneg _) (mul_nonneg (boxVol_nonneg _ _ _) (tsum_nonneg fun _ =>
      Finset.prod_nonneg fun _ _ => norm_nonneg _))
  refine ⟨∑ S ∈ treesOfOrder N, B S, Finset.sum_nonneg (fun S _ => hB S), ?_⟩
  intro t ht
  have hsum : Summable fun n => ∑ S ∈ treesOfOrder N, ‖treeTerm L γ δ p S c t n‖ :=
    summable_sum fun S _ => summable_norm_treeTerm L γ δ p S hc t
  calc
    _ ≤ ∑' n, ∑ S ∈ treesOfOrder N, ‖treeTerm L γ δ p S c t n‖ :=
      Summable.tsum_le_tsum (fun n => by rw [treeTermN_eq_sum]; exact norm_sum_le _ _)
        (summable_norm_treeTermN L γ δ p N hc t) hsum
    _ = ∑ S ∈ treesOfOrder N, ∑' n, ‖treeTerm L γ δ p S c t n‖ :=
      Summable.tsum_finsetSum fun S _ => summable_norm_treeTerm L γ δ p S hc t
    _ ≤ _ := Finset.sum_le_sum fun S _ => tsum_norm_treeTerm_le L γ δ p S hc ht

/-- The clamped remainder is continuous in every coefficient. -/
theorem continuous_zExtend {d p : ℕ} {L Λ : ℝ} {b : ZTime p → (Fin d → ℤ) → ℂ}
    (hb : b ∈ ZSpace L Λ p) (n : Fin d → ℤ) :
    Continuous fun t => IccExtend (by linarith : (p : ℝ) ≤ p + 1) b t n :=
  continuous_IccExtend_iff.mpr (hb.1 n)

/-- The remainder has a uniform summable envelope even after clamping time. -/
theorem exists_zExtend_envelope {d p : ℕ} {L Λ : ℝ} (hL : 0 < L)
    {b : ZTime p → (Fin d → ℤ) → ℂ} (hb : b ∈ ZSpace L Λ p) (hΛ : (d : ℝ) + 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t n,
      ‖IccExtend (by linarith : (p : ℝ) ≤ p + 1) b t n‖ ≤
        C * ((1 + ‖n‖) ^ (d + 1))⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := NLS.IsAkBounded.exists_norm_le hL (zSpace_extended_class (T := p+1) hb hΛ)
  refine ⟨C, hC0, fun t n => ?_⟩
  let s : ZTime p := projIcc (p : ℝ) (p + 1) (by linarith) t
  have hs : s.1 ∈ Icc (0 : ℝ) (p + 1) := ⟨(Nat.cast_nonneg p).trans s.2.1, s.2.2⟩
  have h := hC s.1 hs n
  rw [IccExtend_of_mem _ b s.2] at h
  exact h

/-- Absolute lattice sums of the clamped Z remainder are uniformly bounded. -/
theorem exists_tsum_zExtend_bound {d p : ℕ} {L Λ : ℝ} (hL : 0 < L)
    {b : ZTime p → (Fin d → ℤ) → ℂ} (hb : b ∈ ZSpace L Λ p) (hΛ : (d : ℝ) + 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t,
      (∑' n, ‖IccExtend (by linarith : (p : ℝ) ≤ p + 1) b t n‖) ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_zExtend_envelope hL hb hΛ
  refine ⟨C * ∑' n : Fin d → ℤ, ((1 + ‖n‖) ^ (d + 1))⁻¹,
    mul_nonneg hC0 (tsum_nonneg fun _ => by positivity), fun t => ?_⟩
  have hs := NLS.summable_inv_one_add_norm_pow (d := d)
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (hC t) (zSpace_summable hL hb hΛ _) (hs.mul_left C)

end WaveTurbulence.Fixedpt
