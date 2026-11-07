/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.OneSharedSameSign
import Mathlib.Tactic

/-! # Every virtual-star sign pattern in the one-shared-label good count

The first actual triple is mixed. The second can be mixed or all-same;
this distinction is proved internally and never added to a source input.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

/-- Literal two-triple local bound with first mixed and second arbitrary,
including inflated component-sum energy windows. This conditional local
helper does not assume existence of a graph good configuration. -/
theorem signed_shared_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C R : ℝ, 0 < C ∧ ∀ L ≥ R, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ N ≥ (1 : ℝ),
    ∀ (sg : Fin 6 → Bool), SharedMixed sg false →
    ∀ (a b : Fin d → ℤ) (β₁ β₂ : ℝ) (centers : Fin 5 → Mom d) (S : Finset (Fin 5 → (Fin d → ℤ))),
      (∀ k ∈ S, SignedSharedSource L sg a b β₁ β₂ (N*(δ⁻¹*L^(-2*γ))) centers k) →
      (S.card : ℝ) ≤ C*N^2*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by
  classical
  obtain ⟨Cm,Rm,hCm,hM⟩ := signed_shared_mixed_count_bound d hd γ hγ
  obtain ⟨Cs,Rs,_hCs,hA⟩ := signed_shared_same_count_bound d hd γ hγ
  refine ⟨max Cm Cs,max (max Rm Rs) 1,hCm.trans_le (le_max_left _ _),?_⟩
  intro L hL δ hδ N hN sg hmix a b β₁ β₂ centers S hS
  have hLbase : max Rm Rs ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 ≤ L := zero_le_one.trans ((le_max_right _ _).trans hL)
  have hmono {A : ℝ} (hA : A ≤ max Cm Cs) :
      A*N^2*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) ≤
        max Cm Cs*N^2*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hA (sq_nonneg N)) (sq_nonneg δ⁻¹)) (Real.rpow_nonneg hL0 _)
  by_cases hsecond : SharedMixed sg true
  · exact (hM L ((le_max_left Rm Rs).trans hLbase) δ hδ sg hmix hsecond a b β₁ β₂ centers N hN S hS).trans
      (hmono (le_max_left _ _))
  · have hall : sg 3=sg 4 ∧ sg 4=sg 5 := not_not.mp hsecond
    have hNp : 0 < N := zero_lt_one.trans_le hN
    have hδN : δ/N ∈ Set.Ioc (0 : ℝ) 1 := ⟨div_pos hδ.1 hNp,(div_le_one hNp).mpr (hδ.2.trans hN)⟩
    have hτ : (δ/N)⁻¹*L^(-2*γ) = N*(δ⁻¹*L^(-2*γ)) := by rw [inv_div,div_eq_mul_inv]; ring
    have hb := hA L ((le_max_right Rm Rs).trans hLbase) (δ/N) hδN sg hmix hall a b β₁ β₂ centers S
      (fun k hk => by rw [hτ]; exact hS k hk)
    have he : Cs*(δ/N)⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) =
        Cs*N^2*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by rw [inv_div,div_eq_mul_inv]; ring
    exact (hb.trans_eq he).trans (hmono (le_max_right _ _))

end WaveTurbulence.MoleProp
