/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairFiveAlgebra
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairLocalCount
import Mathlib.Tactic

/-! # Five-label paired-star count for DH23 basiccount(4)

The actual affine reconstruction injects the five labels into the proved
coupled triple set. The minus sign in the combined energy is incorporated
in the fixed strip center; there is no extra tolerance loss.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
open CountLemmas

def DoubleFiveSource {d : ℕ} (L : ℝ) (same : Bool) (a b : Fin d → ℤ)
    (β₁ β₂ τ : ℝ) (centers : Fin 5 → Mom d) (k : Fin 5 → (Fin d → ℤ)) : Prop :=
  DoubleFiveMomentum same a b k ∧ (∀ i, NearLattice L (centers i) (k i)) ∧
    |doubleFiveEnergyOne same (fun i => latticePoint L (k i))-β₁| ≤ τ ∧
    |doubleFiveEnergyTwo same (fun i => latticePoint L (k i))-β₂| ≤ τ

theorem latticePoint_doubleFiveLabels {d : ℕ} (L : ℝ) (same : Bool)
    (a b x y z : Fin d → ℤ) :
    (fun i => latticePoint L (doubleFiveLabels same a b x y z i)) =
      doubleFiveLabels same (latticePoint L a) (latticePoint L b)
        (latticePoint L x) (latticePoint L y) (latticePoint L z) := by
  funext i
  cases same <;> fin_cases i <;>
    simp [doubleFiveLabels,WeylSums.latticePoint_add_eq,WeylSums.latticePoint_sub_eq]

theorem doubleFiveCoordinates_injOn {d : ℕ} (same : Bool) (a b : Fin d → ℤ)
    (S : Finset (Fin 5 → (Fin d → ℤ)))
    (hS : ∀ k ∈ S, DoubleFiveMomentum same a b k) :
    Set.InjOn (doubleFiveCoordinates same a b) S := by
  intro k hk k' hk' he
  rw [doubleFiveLabels_reconstruct same a b k (hS k hk),
    doubleFiveLabels_reconstruct same a b k' (hS k' hk')]
  rw [he]

theorem doubleFiveCoordinates_mem_coupledTripleSet {d : ℕ} (L : ℝ) (same : Bool)
    (a b : Fin d → ℤ) (β₁ β₂ τ : ℝ) (hτ : 0 ≤ τ) (centers : Fin 5 → Mom d)
    (k : Fin 5 → (Fin d → ℤ)) (hk : DoubleFiveSource L same a b β₁ β₂ τ centers k) :
    doubleFiveCoordinates same a b k ∈ coupledTripleSet L
      (if same then centers 0-latticePoint L a else centers 2-latticePoint L a)
      (if same then centers 1-latticePoint L a else centers 0-latticePoint L a)
      (centers 4-latticePoint L (a+b)) (latticePoint L b)
      ((‖latticePoint L a‖^2-β₁)/2) ((‖latticePoint L (a+b)‖^2-β₁-β₂)/2) τ
      (if same then 2 else 0) := by
  obtain ⟨hm,hn,h₁,h₂⟩ := hk
  have hrec := doubleFiveLabels_reconstruct same a b k hm
  have hphys : (fun i => latticePoint L (k i)) = doubleFiveLabels same (latticePoint L a)
      (latticePoint L b) (latticePoint L (doubleFiveCoordinates same a b k).1)
      (latticePoint L (doubleFiveCoordinates same a b k).2.1)
      (latticePoint L (doubleFiveCoordinates same a b k).2.2) := by
    conv_lhs => rw [hrec]
    exact latticePoint_doubleFiveLabels L same a b _ _ _
  rw [hphys] at h₁ h₂
  have hcon := doubleFive_coupled_constraints same (latticePoint L a) (latticePoint L b)
    (latticePoint L (doubleFiveCoordinates same a b k).1)
    (latticePoint L (doubleFiveCoordinates same a b k).2.1)
    (latticePoint L (doubleFiveCoordinates same a b k).2.2) β₁ β₂ τ hτ h₁ h₂
  refine ⟨?_,?_,nearLattice_sub_fixed L (centers 4) (k 4) (a+b) (hn 4),hcon.1,?_⟩
  · cases same
    · exact nearLattice_sub_fixed L (centers 2) (k 2) a (hn 2)
    · exact nearLattice_sub_fixed L (centers 0) (k 0) a (hn 0)
  · cases same
    · exact nearLattice_sub_fixed L (centers 0) (k 0) a (hn 0)
    · exact nearLattice_sub_fixed L (centers 1) (k 1) a (hn 1)
  · cases same <;> simpa [WeylSums.latticePoint_add_eq] using hcon.2

/-- DH23 basiccount(4), literal five-label source form, with constants
uniform over arbitrary charges, centers, energy windows and orientations
of the two rungs. -/
theorem double_five_local_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C R : ℝ, 0 < C ∧ ∀ L ≥ R, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (same : Bool) (a b : Fin d → ℤ) (β₁ β₂ : ℝ) (centers : Fin 5 → Mom d),
    ∀ S : Finset (Fin 5 → (Fin d → ℤ)),
      (∀ k ∈ S, DoubleFiveSource L same a b β₁ β₂ (δ⁻¹*L^(-2*γ)) centers k) →
      (S.card : ℝ) ≤ C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by
  classical
  obtain ⟨C,R,hC,hB⟩ := coupledTriple_bound d hd γ hγ
  refine ⟨C,max R 1,hC,?_⟩
  intro L hL δ hδ same a b β₁ β₂ centers S hS
  have hL0 : 0 < L := zero_lt_one.trans_le ((le_max_right R 1).trans hL)
  have hτ : 0 ≤ δ⁻¹*L^(-2*γ) := mul_nonneg (inv_nonneg.mpr hδ.1.le) (Real.rpow_nonneg hL0.le _)
  let α := (‖latticePoint L a‖^2-β₁)/2
  let β := (‖latticePoint L (a+b)‖^2-β₁-β₂)/2
  let ax := if same then centers 0-latticePoint L a else centers 2-latticePoint L a
  let ay := if same then centers 1-latticePoint L a else centers 0-latticePoint L a
  let az := centers 4-latticePoint L (a+b)
  let T := S.image (doubleFiveCoordinates same a b)
  have hcard : T.card = S.card := card_image_of_injOn
    (doubleFiveCoordinates_injOn same a b S (fun k hk => (hS k hk).1))
  obtain ⟨hf,hb⟩ := hB L ((le_max_left R 1).trans hL) δ hδ ax ay az b
    (if same then 2 else 0) α β
  have hsub : (T : Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))) ⊆
      coupledTripleSet L ax ay az (latticePoint L b) α β (δ⁻¹*L^(-2*γ)) (if same then 2 else 0) := by
    intro z hz
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hz
    exact doubleFiveCoordinates_mem_coupledTripleSet L same a b β₁ β₂ _ hτ centers k (hS k hk)
  have hn : T.card ≤ (coupledTripleSet L ax ay az (latticePoint L b) α β
      (δ⁻¹*L^(-2*γ)) (if same then 2 else 0)).ncard := by
    simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub hf
  have hnR : (T.card : ℝ) ≤ (coupledTripleSet L ax ay az (latticePoint L b) α β
      (δ⁻¹*L^(-2*γ)) (if same then 2 else 0)).ncard := by exact_mod_cast hn
  rw [hcard] at hnR
  exact hnR.trans hb

end WaveTurbulence.MoleProp
