/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.OneSharedTripleAlgebra
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairLocalCount
import Mathlib.Tactic

/-! # Conditional five-label good-step counts for DH23 Proposition 10.3

The source inputs are two literal momentum/energy systems, not a counting
estimate. An inflated cut window N times the original tolerance costs only
N squared, with a threshold uniform in N and delta.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
open CountLemmas

def OneSharedSource {d : ℕ} (L : ℝ) (mode : Fin 3) (a b : Fin d → ℤ)
    (β₁ β₂ τ : ℝ) (centers : Fin 5 → Mom d) (k : Fin 5 → (Fin d → ℤ)) : Prop :=
  OneSharedMomentum mode a b k ∧ (∀ i, NearLattice L (centers i) (k i)) ∧
    |oneSharedEnergyOne mode (fun i => latticePoint L (k i))-β₁| ≤ τ ∧
    |oneSharedEnergyTwo mode (fun i => latticePoint L (k i))-β₂| ≤ τ

theorem latticePoint_oneSharedLabels {d : ℕ} (L : ℝ) (mode : Fin 3)
    (a b x y z : Fin d → ℤ) :
    (fun i => latticePoint L (oneSharedLabels mode a b x y z i)) =
      oneSharedLabels mode (latticePoint L a) (latticePoint L b)
        (latticePoint L x) (latticePoint L y) (latticePoint L z) := by
  funext i
  fin_cases mode <;> fin_cases i <;>
    simp [oneSharedLabels,WeylSums.latticePoint_add_eq,WeylSums.latticePoint_sub_eq]

theorem latticePoint_oneSharedOffset {d : ℕ} (L : ℝ) (mode : Fin 3) (a b : Fin d → ℤ) :
    latticePoint L (oneSharedOffset mode a b) = oneSharedOffset mode (latticePoint L a) (latticePoint L b) := by
  unfold oneSharedOffset
  split_ifs
  · change latticePointHom L (-(a+b)) = _
    simp only [map_neg,map_add,latticePointHom_apply]
  · change latticePointHom L (b-a) = _
    simp only [map_sub,latticePointHom_apply]

theorem nearLattice_add_fixed {d : ℕ} (L : ℝ) (center : Mom d) (k a : Fin d → ℤ)
    (h : CountLemmas.NearLattice L center k) : CountLemmas.NearLattice L (center+latticePoint L a) (k+a) := by
  unfold CountLemmas.NearLattice at h ⊢
  rw [WeylSums.latticePoint_add_eq]
  have he : (latticePoint L k+latticePoint L a)-(center+latticePoint L a) = latticePoint L k-center := by abel
  rw [he]
  exact h

theorem oneSharedCoordinates_injOn {d : ℕ} (mode : Fin 3) (a b : Fin d → ℤ)
    (S : Finset (Fin 5 → (Fin d → ℤ))) (hS : ∀ k ∈ S, OneSharedMomentum mode a b k) :
    Set.InjOn (oneSharedCoordinates mode a b) S := by
  intro k hk k' hk' he
  rw [oneSharedLabels_reconstruct mode a b k (hS k hk),oneSharedLabels_reconstruct mode a b k' (hS k' hk')]
  rw [he]

theorem oneSharedCoordinates_mem_coupledTripleSet {d : ℕ} (L : ℝ) (mode : Fin 3)
    (a b : Fin d → ℤ) (β₁ β₂ τ : ℝ) (hτ : 0 ≤ τ) (centers : Fin 5 → Mom d)
    (k : Fin 5 → (Fin d → ℤ)) (hk : OneSharedSource L mode a b β₁ β₂ τ centers k) :
    oneSharedCoordinates mode a b k ∈ coupledTripleSet L
      (if mode=0 then centers 0-latticePoint L a else centers 1-latticePoint L a)
      (centers 2-latticePoint L a)
      (if mode=0 then centers 4+latticePoint L b else centers 3-latticePoint L b)
      (latticePoint L (oneSharedOffset mode a b)) ((‖latticePoint L a‖^2-β₁)/2)
      (if mode=0 then (β₂+‖latticePoint L b‖^2)/2 else (‖latticePoint L b‖^2-β₂)/2) τ mode := by
  obtain ⟨hm,hn,h₁,h₂⟩ := hk
  have hrec := oneSharedLabels_reconstruct mode a b k hm
  have hphys : (fun i => latticePoint L (k i)) = oneSharedLabels mode (latticePoint L a) (latticePoint L b)
      (latticePoint L (oneSharedCoordinates mode a b k).1)
      (latticePoint L (oneSharedCoordinates mode a b k).2.1)
      (latticePoint L (oneSharedCoordinates mode a b k).2.2) := by
    conv_lhs => rw [hrec]
    exact latticePoint_oneSharedLabels L mode a b _ _ _
  rw [hphys] at h₁ h₂
  have hcon := oneShared_coupled_constraints mode (latticePoint L a) (latticePoint L b)
    (latticePoint L (oneSharedCoordinates mode a b k).1)
    (latticePoint L (oneSharedCoordinates mode a b k).2.1)
    (latticePoint L (oneSharedCoordinates mode a b k).2.2) β₁ β₂ τ hτ h₁ h₂
  refine ⟨?_,nearLattice_sub_fixed L (centers 2) (k 2) a (hn 2),?_,hcon.1,?_⟩
  · by_cases hmode : mode=0
    · simpa only [oneSharedCoordinates,hmode,ite_true] using nearLattice_sub_fixed L (centers 0) (k 0) a (hn 0)
    · simpa only [oneSharedCoordinates,hmode,ite_false] using nearLattice_sub_fixed L (centers 1) (k 1) a (hn 1)
  · by_cases hmode : mode=0
    · simpa only [oneSharedCoordinates,hmode,ite_true] using nearLattice_add_fixed L (centers 4) (k 4) b (hn 4)
    · simpa only [oneSharedCoordinates,hmode,ite_false] using nearLattice_sub_fixed L (centers 3) (k 3) b (hn 3)
  · simpa only [latticePoint_oneSharedOffset] using hcon.2

/-- Conditional local good-step helper for two three-label equations
sharing one label. The three modes are exact coupled-triple selectors. -/
theorem one_shared_local_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C R : ℝ, 0 < C ∧ ∀ L ≥ R, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (mode : Fin 3) (a b : Fin d → ℤ) (β₁ β₂ : ℝ) (centers : Fin 5 → Mom d)
      (S : Finset (Fin 5 → (Fin d → ℤ))),
      (∀ k ∈ S, OneSharedSource L mode a b β₁ β₂ (δ⁻¹*L^(-2*γ)) centers k) →
      (S.card : ℝ) ≤ C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by
  classical
  obtain ⟨C,R,hC,hB⟩ := coupledTriple_bound d hd γ hγ
  refine ⟨C,max R 1,hC,?_⟩
  intro L hL δ hδ mode a b β₁ β₂ centers S hS
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right R 1).trans hL)
  have hτ : 0 ≤ δ⁻¹*L^(-2*γ) := mul_nonneg (inv_nonneg.mpr hδ.1.le) (Real.rpow_nonneg hLp.le _)
  let ax := if mode=0 then centers 0-latticePoint L a else centers 1-latticePoint L a
  let ay := centers 2-latticePoint L a
  let az := if mode=0 then centers 4+latticePoint L b else centers 3-latticePoint L b
  let α := (‖latticePoint L a‖^2-β₁)/2
  let β := if mode=0 then (β₂+‖latticePoint L b‖^2)/2 else (‖latticePoint L b‖^2-β₂)/2
  let T := S.image (oneSharedCoordinates mode a b)
  have hcard : T.card = S.card := card_image_of_injOn
    (oneSharedCoordinates_injOn mode a b S (fun k hk => (hS k hk).1))
  obtain ⟨hf,hb⟩ := hB L ((le_max_left R 1).trans hL) δ hδ ax ay az (oneSharedOffset mode a b) mode α β
  have hsub : (T : Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))) ⊆
      coupledTripleSet L ax ay az (latticePoint L (oneSharedOffset mode a b)) α β (δ⁻¹*L^(-2*γ)) mode := by
    intro z hz
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hz
    exact oneSharedCoordinates_mem_coupledTripleSet L mode a b β₁ β₂ _ hτ centers k (hS k hk)
  have hn : T.card ≤ (coupledTripleSet L ax ay az (latticePoint L (oneSharedOffset mode a b)) α β
      (δ⁻¹*L^(-2*γ)) mode).ncard := by simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub hf
  have hnR : (T.card : ℝ) ≤ (coupledTripleSet L ax ay az (latticePoint L (oneSharedOffset mode a b)) α β
      (δ⁻¹*L^(-2*γ)) mode).ncard := by exact_mod_cast hn
  rw [hcard] at hnR
  exact hnR.trans hb

/-- An N-fold source cut-energy window costs N squared, with constants
and threshold still uniform in N. This is not a graph good-step theorem. -/
theorem one_shared_inflated_window_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C R : ℝ, 0 < C ∧ ∀ L ≥ R, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ N ≥ (1 : ℝ),
    ∀ (mode : Fin 3) (a b : Fin d → ℤ) (β₁ β₂ : ℝ) (centers : Fin 5 → Mom d)
      (S : Finset (Fin 5 → (Fin d → ℤ))),
      (∀ k ∈ S, OneSharedSource L mode a b β₁ β₂ (N*(δ⁻¹*L^(-2*γ))) centers k) →
      (S.card : ℝ) ≤ C*N^2*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by
  obtain ⟨C,R,hC,hB⟩ := one_shared_local_count_bound d hd γ hγ
  refine ⟨C,R,hC,?_⟩
  intro L hL δ hδ N hN mode a b β₁ β₂ centers S hS
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hδN : δ/N ∈ Set.Ioc (0 : ℝ) 1 := ⟨div_pos hδ.1 hNp,(div_le_one hNp).mpr (hδ.2.trans hN)⟩
  have hτ : (δ/N)⁻¹*L^(-2*γ) = N*(δ⁻¹*L^(-2*γ)) := by rw [inv_div,div_eq_mul_inv]; ring
  have hb := hB L hL (δ/N) hδN mode a b β₁ β₂ centers S (fun k hk => by rw [hτ]; exact hS k hk)
  have he : C*(δ/N)⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) =
      C*N^2*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by rw [inv_div,div_eq_mul_inv]; ring
  exact hb.trans_eq he

end WaveTurbulence.MoleProp
