/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairAlgebra
import Mathlib.Tactic

/-! # Literal four-label paired-star count for DH23 basiccount(3)

The canonical equal-rung and opposite-rung systems inject into the actual
coupled pair set. The gap parameter needs only the lower comparison,
including at P=1, as in the proved counting interface.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
open CountLemmas

/-- The literal four-label source system, with two fixed momentum values,
two actual energy windows, and four independent unit-ball centers. -/
def DoublePairSource {d : ℕ} (L : ℝ) (same : Bool) (a b : Fin d → ℤ)
    (β₁ β₂ τ : ℝ) (centers : Fin 4 → Mom d) (k : Fin 4 → (Fin d → ℤ)) : Prop :=
  DoublePairMomentum same a b k ∧ (∀ i, NearLattice L (centers i) (k i)) ∧
    |doublePairEnergyOne same (fun i => latticePoint L (k i))-β₁| ≤ τ ∧
    |doublePairEnergyTwo same (fun i => latticePoint L (k i))-β₂| ≤ τ

theorem latticePoint_doublePairLabels {d : ℕ} (L : ℝ) (same : Bool)
    (a b x y : Fin d → ℤ) :
    (fun i => latticePoint L (doublePairLabels same a b x y i)) =
      doublePairLabels same (latticePoint L a) (latticePoint L b) (latticePoint L x) (latticePoint L y) := by
  funext i
  cases same <;> fin_cases i <;>
    simp [doublePairLabels,WeylSums.latticePoint_add_eq,WeylSums.latticePoint_sub_eq]

theorem nearLattice_sub_fixed {d : ℕ} (L : ℝ) (center : Mom d) (k a : Fin d → ℤ)
    (h : NearLattice L center k) :
    NearLattice L (center-latticePoint L a) (k-a) := by
  unfold NearLattice at h ⊢
  rw [WeylSums.latticePoint_sub_eq]
  have he : (latticePoint L k-latticePoint L a)-(center-latticePoint L a) = latticePoint L k-center := by abel
  rw [he]
  exact h

/-- Coordinates determine all four literal labels on each fixed-momentum
source family, without a finite multiplicity factor. -/
theorem doublePairCoordinates_injOn {d : ℕ} (same : Bool) (a b : Fin d → ℤ)
    (S : Finset (Fin 4 → (Fin d → ℤ)))
    (hS : ∀ k ∈ S, DoublePairMomentum same a b k) :
    Set.InjOn (doublePairCoordinates same a) S := by
  intro k hk k' hk' he
  rw [doublePairLabels_reconstruct same a b k (hS k hk),
    doublePairLabels_reconstruct same a b k' (hS k' hk')]
  rw [he]

/-- Actual four-label source constraints imply membership of the proved
coupled-pair set, with selector y or x+y according to rung orientation. -/
theorem doublePairCoordinates_mem_coupledPairSet {d : ℕ} (L : ℝ) (same : Bool)
    (a b : Fin d → ℤ) (β₁ β₂ τ : ℝ) (hτ : 0 ≤ τ) (centers : Fin 4 → Mom d)
    (k : Fin 4 → (Fin d → ℤ)) (hk : DoublePairSource L same a b β₁ β₂ τ centers k) :
    doublePairCoordinates same a k ∈ coupledPairSet L (centers 0-latticePoint L a)
      (if same then centers 1-latticePoint L a else centers 2-latticePoint L a)
      (latticePoint L (a+b)) ((‖latticePoint L a‖^2-β₁)/2)
      ((β₁+β₂-2*inner ℝ (latticePoint L (a+b)) (latticePoint L a)-
        (if same then 1 else -1)*‖latticePoint L (a+b)‖^2)/2) τ (if same then 2 else 1) := by
  obtain ⟨hm,hn,h₁,h₂⟩ := hk
  have hrec := doublePairLabels_reconstruct same a b k hm
  have hphys : (fun i => latticePoint L (k i)) = doublePairLabels same (latticePoint L a)
      (latticePoint L b) (latticePoint L (doublePairCoordinates same a k).1)
      (latticePoint L (doublePairCoordinates same a k).2) := by
    conv_lhs => rw [hrec]
    exact latticePoint_doublePairLabels L same a b _ _
  rw [hphys] at h₁ h₂
  have hcon := doublePair_coupled_constraints same (latticePoint L a) (latticePoint L b)
    (latticePoint L (doublePairCoordinates same a k).1)
    (latticePoint L (doublePairCoordinates same a k).2) β₁ β₂ τ hτ h₁ h₂
  refine ⟨nearLattice_sub_fixed L (centers 0) (k 0) a (hn 0),?_,hcon.1,?_⟩
  · cases same
    · exact nearLattice_sub_fixed L (centers 2) (k 2) a (hn 2)
    · exact nearLattice_sub_fixed L (centers 1) (k 1) a (hn 1)
  · cases same <;> simpa [WeylSums.latticePoint_add_eq] using hcon.2

/-- DH23 basiccount(3), literal four-label version. The constant is uniform
in both momentum charges, all four centers, all energy centers, and the
rail gap scale. Its threshold may depend on the fixed delta. -/
theorem double_pair_local_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (c : ℝ) (hc : 1 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ (same : Bool) (a b : Fin d → ℤ) (β₁ β₂ : ℝ) (centers : Fin 4 → Mom d) (P : ℝ),
      (P = 0 ∨ P ∈ Set.Icc L⁻¹ 1) → (0 < P → c⁻¹*P ≤ ‖latticePoint L (a+b)‖) →
    ∀ S : Finset (Fin 4 → (Fin d → ℤ)),
      (∀ k ∈ S, DoublePairSource L same a b β₁ β₂ (δ⁻¹*L^(-2*γ)) centers k) →
      (S.card : ℝ) ≤ C*δ⁻¹*L^(2*((d : ℝ)-γ))*(min (Real.log L^2) (1+δ*L^(2*γ)*P))⁻¹ := by
  classical
  obtain ⟨C,hC,hB⟩ := coupledPair_bound d hd γ hγ c hc
  refine ⟨C,hC,?_⟩
  intro δ hδ
  obtain ⟨R,hR⟩ := hB δ hδ
  refine ⟨max R 1,?_⟩
  intro L hL same a b β₁ β₂ centers P hP hgap S hS
  have hL0 : 0 < L := zero_lt_one.trans_le ((le_max_right R 1).trans hL)
  have hτ : 0 ≤ δ⁻¹*L^(-2*γ) := mul_nonneg (inv_nonneg.mpr hδ.1.le) (Real.rpow_nonneg hL0.le _)
  let α := (‖latticePoint L a‖^2-β₁)/2
  let β := (β₁+β₂-2*inner ℝ (latticePoint L (a+b)) (latticePoint L a)-
    (if same then 1 else -1)*‖latticePoint L (a+b)‖^2)/2
  let ax := centers 0-latticePoint L a
  let ay := if same then centers 1-latticePoint L a else centers 2-latticePoint L a
  let T := S.image (doublePairCoordinates same a)
  have hcard : T.card = S.card := card_image_of_injOn
    (doublePairCoordinates_injOn same a b S (fun k hk => (hS k hk).1))
  obtain ⟨hf,hb⟩ := hR L ((le_max_left R 1).trans hL) ax ay (latticePoint L (a+b)) α β
    (if same then 2 else 1) P hP hgap
  have hsub : (T : Set ((Fin d → ℤ) × (Fin d → ℤ))) ⊆
      coupledPairSet L ax ay (latticePoint L (a+b)) α β (δ⁻¹*L^(-2*γ)) (if same then 2 else 1) := by
    intro z hz
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hz
    exact doublePairCoordinates_mem_coupledPairSet L same a b β₁ β₂ _ hτ centers k (hS k hk)
  have hn : T.card ≤ (coupledPairSet L ax ay (latticePoint L (a+b)) α β
      (δ⁻¹*L^(-2*γ)) (if same then 2 else 1)).ncard := by
    simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub hf
  have hnR : (T.card : ℝ) ≤ (coupledPairSet L ax ay (latticePoint L (a+b)) α β
      (δ⁻¹*L^(-2*γ)) (if same then 2 else 1)).ncard := by exact_mod_cast hn
  rw [hcard] at hnR
  exact hnR.trans hb

end WaveTurbulence.MoleProp
