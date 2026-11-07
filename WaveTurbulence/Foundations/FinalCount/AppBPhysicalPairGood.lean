/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPhysicalPair
public import WaveTurbulence.Foundations.FinalCount.AppBPairGoodGain
import Mathlib.Tactic

/-! # Good power saving for actual physical pair fibers -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset Filter CountLemmas

/-- Actual pair good gain, including prescribed real momentum and either
relative sign. The opposite-sign premise is the source internal-gap test. -/
theorem appb_physical_pair_good_bound (d : ℕ) (hd : 2 ≤ d) (δ γ : ℝ)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (m : ℕ) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ w a b momentum : Mom d, ∀ β : ℝ, ∀ ε : ℤˣ,
    ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, ‖w+latticePoint L q.1-a‖ ≤ 1 ∧ ‖w+latticePoint L q.2-b‖ ≤ 1 ∧
        (w+latticePoint L q.1)+(ε : ℤ) • (w+latticePoint L q.2) = momentum ∧
        |‖w+latticePoint L q.1‖^2+(ε : ℤ)*‖w+latticePoint L q.2‖^2-β| ≤ appbWidth δ γ m L) →
      (ε = -1 → ∀ q ∈ s, L^(-γ+2*min γ (1-γ)/3) ≤
        ‖(w+latticePoint L q.1)-(w+latticePoint L q.2)‖) →
      (s.card : ℝ) ≤ L^((d : ℝ)-γ-31*min γ (1-γ)/48) := by
  obtain ⟨Lp,hLp0⟩ := appb_positive_pair_good_gain d hd δ γ hδ hγ m
  obtain ⟨Ln,hLn⟩ := appb_negative_pair_good_gain d (by omega) δ γ hδ hγ m
  refine ⟨max Lp (max Ln 1),?_⟩
  intro L hL w a b momentum β ε s hs hgap
  have hL1 : 1 ≤ L := (le_max_right Ln 1).trans ((le_max_right Lp _).trans hL)
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
    · exact hLp0 L ((le_max_left Lp _).trans hL) w a b nk β
    · have hg : L^(-γ+2*min γ (1-γ)/3) ≤ ‖latticePoint L nk‖ := by
        have hh := hgap rfl q₀ hq₀
        have he : latticePoint L nk = (w+latticePoint L q₀.1)-(w+latticePoint L q₀.2) := by
          dsimp only [nk]
          simp only [Units.val_neg,Units.val_one,neg_smul,one_smul,← sub_eq_add_neg,
            WeylSums.latticePoint_sub_eq]
          abel
        simpa only [he] using hh
      exact hLn L ((le_max_left Ln _).trans ((le_max_right Lp _).trans hL)) w a b nk β hg
  · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hnon
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

end WaveTurbulence.Mole
