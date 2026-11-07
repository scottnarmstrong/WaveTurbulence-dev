/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCosetTriples
public import WaveTurbulence.Foundations.FinalCount.AppBPhysicalPair
import Mathlib.Tactic

/-! # Triple counting with prescribed physical momentum on an affine coset -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset CountLemmas

/-- Equal signed physical triple momentum fixes the actual integer triple
momentum, uniformly in the prescribed source and the affine lattice shift. -/
theorem appb_triple_integer_momentum {d : ℕ} {L : ℝ} (hL : L ≠ 0) (w : Mom d)
    (a b : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))
    (hm : (w+latticePoint L a.1)-(w+latticePoint L a.2.1)+(w+latticePoint L a.2.2) =
      (w+latticePoint L b.1)-(w+latticePoint L b.2.1)+(w+latticePoint L b.2.2)) :
    a.1-a.2.1+a.2.2 = b.1-b.2.1+b.2.2 := by
  apply appb_latticePoint_injective hL
  rw [WeylSums.latticePoint_add_eq,WeylSums.latticePoint_add_eq,
    WeylSums.latticePoint_sub_eq,WeylSums.latticePoint_sub_eq]
  apply add_left_cancel (a := w)
  calc
    _ = (w+latticePoint L a.1)-(w+latticePoint L a.2.1)+(w+latticePoint L a.2.2) := by abel
    _ = (w+latticePoint L b.1)-(w+latticePoint L b.2.1)+(w+latticePoint L b.2.2) := hm
    _ = _ := by abel

/-- DH23 basiccount(2), for the actual finite tuples at a fixed physical
source. The constant and threshold are uniform in all source parameters. -/
theorem appb_physical_triple_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L ≥ L₀, 0 < L → ∀ δ ∈ Ioc (0 : ℝ) 1,
    ∀ w a b c momentum : Mom d, ∀ β : ℝ,
    ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, ‖w+latticePoint L q.1-a‖ ≤ 1 ∧ ‖w+latticePoint L q.2.1-b‖ ≤ 1 ∧
        ‖w+latticePoint L q.2.2-c‖ ≤ 1 ∧
        (w+latticePoint L q.1)-(w+latticePoint L q.2.1)+(w+latticePoint L q.2.2) = momentum ∧
        |‖w+latticePoint L q.1‖^2-‖w+latticePoint L q.2.1‖^2+‖w+latticePoint L q.2.2‖^2-β| ≤
          δ⁻¹*L^(-2*γ)) →
      (s.card : ℝ) ≤ C*δ⁻¹*L^(2*((d : ℝ)-γ)) := by
  obtain ⟨C,L₀,hbound⟩ := appb_coset_triple_bound d hd γ hγ
  refine ⟨max C 1,L₀,lt_of_lt_of_le zero_lt_one (le_max_right C 1),?_⟩
  intro L hL hLp δ hδ w a b c momentum β s hs
  by_cases hn : s.Nonempty
  · obtain ⟨q₀,hq₀⟩ := hn
    let nk := q₀.1-q₀.2.1+q₀.2.2
    have hsub : (s : Set _) ⊆ appbCosetTripleSet L w a b c nk β (δ⁻¹*L^(-2*γ)) := by
      intro q hq
      have hh := hs q hq
      exact ⟨hh.1,hh.2.1,hh.2.2.1,
        appb_triple_integer_momentum hLp.ne' w q q₀ (hh.2.2.2.1.trans (hs q₀ hq₀).2.2.2.1.symm),hh.2.2.2.2⟩
    obtain ⟨hfinite,hcount⟩ := hbound L hL δ hδ w a b c nk β
    have hc : (s.card : ℝ) ≤ ((appbCosetTripleSet L w a b c nk β (δ⁻¹*L^(-2*γ))).ncard : ℝ) := by
      exact Nat.cast_le.mpr (by simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub hfinite)
    exact hc.trans (hcount.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left C 1) (inv_nonneg.mpr hδ.1.le)) (by positivity)))
  · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hn
    rw [he,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (zero_le_one.trans (le_max_right C 1))
      (inv_nonneg.mpr hδ.1.le)) (Real.rpow_nonneg hLp.le _)

end WaveTurbulence.Mole
