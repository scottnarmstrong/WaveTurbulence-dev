/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.IncoherentPointwise
public import WaveTurbulence.Foundations.Spine.RegularLayeringCount
public import WaveTurbulence.Foundations.Spine.FiniteCoverSum
/-! TARGET L2230–2232: assemble B2.2, source regular-object counting, and C4 over the actual truncated sum. -/
public section
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open WaveTurbulence.Reg WaveTurbulence.Links
open Set Finset

/-- The full finite incoherent contribution is controlled by its genuine incoherency count sum.
Truncation is kept in the left carrier and discarded only when enlarging a nonnegative upper bound. -/
theorem norm_incoherentCoupleSum_le_counted (P : WTParams) (hdecay : IncoherentDecayAt P)
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη : 0 ≤ P.η) (hC₁ : 0 ≤ P.C₁) (hδ : 0 ≤ P.δ)
    {p n : ℕ} (hp : p < P.D) (R : ℕ → Mom P.d → ℝ) (hR : RemainderBound P R p)
    (hn : n ≤ P.N (p + 1) ^ 4) (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) (k : Mom P.d) :
    ‖incoherentCoupleSum P (inputsF P R) (p + 1) (2 * n) t k‖ ≤
      ∑ g ∈ (range (n + 1)).filter (fun g => 1 ≤ g),
        (((12 ^ 9) ^ n * ((2 ^ (9 * p)) ^ g * 2 ^ (2 * n)) : ℕ) : ℝ) *
          (P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * g)) := by
  classical
  let S : ℕ → Finset (LayeredGarden 2) := fun g => (finite_regularLayeredCouplesAt p n g).toFinset
  have hcover : ∀ LG ∈ (coupleCarrier P (p + 1) (2 * n)).filter
      (fun LG => IsRegularCouple LG.garden ∧ ¬ IsCoherentCouple LG),
      ∃ g ∈ (range (n + 1)).filter (fun g => 1 ≤ g), LG ∈ S g := by
    intro LG hLG
    obtain ⟨hm, hreg, hnc⟩ := mem_filter.mp hLG
    have hmem := (Canon.finite_truncSumC_support P (p + 1) (2 * n)).mem_toFinset.mp hm
    obtain ⟨Q, hw, hQ⟩ := isRegularCouple_exists_wf_decodes LG.garden hreg
    have hsize : Q.size = 2 * n := (size_eq_order hQ).symm.trans hmem.2.2
    have hg0 : 1 ≤ LG.incoherency Q.links := by
      by_contra h
      exact hnc ⟨hreg, Q, hw, hQ, by omega⟩
    have hg1 : LG.incoherency Q.links ≤ n := by
      have h := incoherency_le hQ
      omega
    refine ⟨LG.incoherency Q.links, mem_filter.mpr ⟨mem_range.mpr (by omega), hg0⟩, ?_⟩
    change LG ∈ (finite_regularLayeredCouplesAt p n (LG.incoherency Q.links)).toFinset
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_iUnion.mpr ⟨⟨Q, hw, hsize⟩, hmem.1, hQ, rfl⟩
  unfold incoherentCoupleSum
  apply norm_sum_le_cover_count _ _ S _ _ _ hcover
  · intro g _
    exact mul_nonneg (mul_nonneg hC₁ (pow_nonneg (mul_nonneg hC₁ hδ) _))
      (Real.rpow_nonneg (by linarith) _)
  · intro g _
    have h := ncard_regularLayeredCouplesAt_le p n g
    rw [Set.ncard_eq_toFinset_card _ (finite_regularLayeredCouplesAt p n g)] at h
    exact_mod_cast h
  · intro g hg LG hLG
    have hg0 := (mem_filter.mp hg).2
    have hmem : LG ∈ regularLayeredCouplesAt p n g :=
      (finite_regularLayeredCouplesAt p n g).mem_toFinset.mp hLG
    obtain ⟨Q, hcan, hQ, hind⟩ := Set.mem_iUnion.mp hmem
    have h := norm_incoherent_couple_le P hdecay hd hL hη hC₁ hδ hp R hR hn Q.1 Q.2.1 Q.2.2
      LG hcan hQ (by omega) t ht k
    simpa only [hind] using h

end WaveTurbulence.LGSpine
