/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPhysicalPair
public import WaveTurbulence.Foundations.FinalCount.AppBPairGoodGain
import Mathlib.Tactic

/-! # Fine power saving for actual physical pair fibers -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset Filter CountLemmas

/-- DH23 basiccount(1) in the form consumed by degree-two removal:
fixed physical momentum, actual finite labels, and LG for opposite signs.
The 3 eta/4 saving leaves room for normalization constants. -/
theorem appb_physical_pair_fine_bound (d : ℕ) (hd : 2 ≤ d) (δ γ η : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (hη : 0 < η) (hηγ : η ≤ min γ (1-γ)) (m : ℕ) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ w a b momentum : Mom d, ∀ β : ℝ, ∀ ε : ℤˣ,
    ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, ‖w+latticePoint L q.1-a‖ ≤ 1 ∧ ‖w+latticePoint L q.2-b‖ ≤ 1 ∧
        (w+latticePoint L q.1)+(ε : ℤ) • (w+latticePoint L q.2) = momentum ∧
        |‖w+latticePoint L q.1‖^2+(ε : ℤ)*‖w+latticePoint L q.2‖^2-β| ≤ appbWidth δ γ m L) →
      (ε = -1 → ∀ q ∈ s, L^(-γ+η) ≤
        ‖(w+latticePoint L q.1)-(w+latticePoint L q.2)‖) →
      (s.card : ℝ) ≤ L^((d : ℝ)-γ-3*η/4) := by
  have hp := appb_log_coefficient_eventual (2*3^(d-2)*(6*Real.pi+1284002)) δ
    ((d : ℝ)-γ-min γ (1-γ)) ((d : ℝ)-γ-3*η/4) m
    (by linarith only [hη,hηγ])
  have hn := appb_log_coefficient_eventual (3^(d-1)*((d : ℝ)+1)) δ
    ((d : ℝ)-γ-η) ((d : ℝ)-γ-3*η/4) m (by linarith only [hη])
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp ((hp.and hn).and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨L₀,?_⟩
  intro L hL w a b momentum β ε s hs hgap
  obtain ⟨⟨hpL,hnL⟩,hL1⟩ := hL₀ L hL
  have hLp := zero_lt_one.trans_le hL1
  by_cases hnon : s.Nonempty
  · obtain ⟨q₀,hq₀⟩ := hnon
    let nk := q₀.1+(ε : ℤ) • q₀.2
    have hsub := appb_physical_pair_subset hLp.ne' w a b momentum β (appbWidth δ γ m L) ε s hs hq₀
    have hc : (s.card : ℝ) ≤ ((appbCosetPairSet L w a b nk β (appbWidth δ γ m L) ε).ncard : ℝ) := by
      exact_mod_cast (by simpa only [Set.ncard_coe_finset] using
        Set.ncard_le_ncard hsub (appb_cosetPairSet_finite hLp w a b nk β _ ε))
    refine hc.trans ?_
    rcases Int.units_eq_one_or ε with rfl | rfl
    · exact (appb_coset_positive_pair_log_window_bound hd hL1 hδ hγ.2.le m w a b nk β).trans hpL
    · have hg : L^(-γ+η) ≤ ‖latticePoint L nk‖ := by
        have hh := hgap rfl q₀ hq₀
        have he : latticePoint L nk = (w+latticePoint L q₀.1)-(w+latticePoint L q₀.2) := by
          dsimp only [nk]
          simp only [Units.val_neg,Units.val_one,neg_smul,one_smul,← sub_eq_add_neg,
            WeylSums.latticePoint_sub_eq]
          abel
        simpa only [he] using hh
      exact (appb_coset_negative_pair_log_window_bound (by omega) hL1 hδ
        (hηγ.trans (min_le_right γ (1-γ))) m w a b nk β hg).trans hnL
  · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hnon
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

end WaveTurbulence.Mole
