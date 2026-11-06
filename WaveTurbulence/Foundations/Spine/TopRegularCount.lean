/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentFiniteCarrier
public import WaveTurbulence.Foundations.Spine.RegularLayeringCount
/-! Uniform exponential enumeration of the actual coherent carriers, at every truncation order. -/
public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Reg
open Set Finset
open scoped Classical

theorem topRegularCarrier_subset_zero_incoherency (p n : ℕ) :
    topRegularCarrier p (2 * n) ⊆ regularLayeredCouplesAt p n 0 := by
  intro LG hLG
  have hc := (coherent_canonical_iff_regular_uniform LG p).mpr ⟨hLG.1, hLG.2.2⟩
  obtain ⟨_, Q, hw, hQ, hi⟩ := hc.2
  have hsize : Q.size = 2 * n := (size_eq_order hQ).symm.trans hLG.2.1
  exact Set.mem_iUnion.mpr ⟨⟨Q, hw, hsize⟩, hc.1, hQ, hi⟩

theorem ncard_topRegularCarrier_le (p n : ℕ) :
    (topRegularCarrier p (2 * n)).ncard ≤ ((12 ^ 9) * 4) ^ n := by
  have h := (Set.ncard_le_ncard (topRegularCarrier_subset_zero_incoherency p n)
    (finite_regularLayeredCouplesAt p n 0)).trans (ncard_regularLayeredCouplesAt_le p n 0)
  calc
    _ ≤ (12 ^ 9) ^ n * 2 ^ (2 * n) := by simpa only [pow_zero, one_mul] using h
    _ = ((12 ^ 9) * 4) ^ n := by
      rw [mul_pow, show (2 : ℕ) ^ (2 * n) = 4 ^ n by rw [pow_mul]; norm_num]

/-- The cutoff can only remove terms from this positive carrier count; the bound also applies
in the intermediate and high-order coherent ranges where comparison with the full sum fails. -/
theorem card_coherent_carrier_le (P : WTParams) (p n : ℕ) :
    ((coupleCarrier P (p + 1) (2 * n)).filter IsCoherentCouple).card ≤ ((12 ^ 9) * 4) ^ n := by
  classical
  have hs : (coupleCarrier P (p + 1) (2 * n)).filter IsCoherentCouple ⊆
      (finite_topRegularCarrier p (2 * n)).toFinset := by
    intro LG hLG
    obtain ⟨hm, hc⟩ := mem_filter.mp hLG
    have hmem := (Canon.finite_truncSumC_support P (p + 1) (2 * n)).mem_toFinset.mp hm
    rw [Set.Finite.mem_toFinset]
    exact ⟨hc.1, hmem.2.2, coherent_canonical_layer_eq hmem.1 hc⟩
  apply (Finset.card_le_card hs).trans
  have h := ncard_topRegularCarrier_le p n
  rwa [Set.ncard_eq_toFinset_card _ (finite_topRegularCarrier p (2 * n))] at h

end WaveTurbulence.LGSpine
