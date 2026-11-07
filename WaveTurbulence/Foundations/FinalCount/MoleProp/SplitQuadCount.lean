/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.LargeGapPair
import Mathlib.Tactic

/-! # Two actual mixed pairs with cut-inflated energy windows

This conditional analytic helper is for the direct beta-plus-removal step.
The charge and cut-energy hypotheses must be produced from an actual old
cut before it is used in a source operation bound.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
open CountLemmas

def SplitQuadSource {d : ℕ} (L : ℝ) (q1 q2 : Fin d → ℤ)
    (β1 β2 τ : ℝ) (centers : Fin 4 → Mom d) (k : Fin 4 → (Fin d → ℤ)) : Prop :=
  k 0-k 1=q1 ∧ k 2-k 3=q2 ∧ (∀ i, NearLattice L (centers i) (k i)) ∧
    |‖latticePoint L (k 0)‖^2-‖latticePoint L (k 1)‖^2-β1| ≤ τ ∧
    |‖latticePoint L (k 2)‖^2-‖latticePoint L (k 3)‖^2-β2| ≤ τ

theorem split_quad_local_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ C R : ℝ, 0 ≤ C ∧ ∀ L ≥ R, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ N ≥ (1 : ℝ), ∀ (q1 q2 : Fin d → ℤ) (β1 β2 : ℝ) (centers : Fin 4 → Mom d),
      L^(-γ+η) ≤ ‖latticePoint L q1‖ → L^(-γ+η) ≤ ‖latticePoint L q2‖ →
    ∀ F : Finset (Fin 4 → (Fin d → ℤ)),
      (∀ k ∈ F, SplitQuadSource L q1 q2 β1 β2 (N*(δ⁻¹*L^(-2*γ))) centers k) →
      (F.card : ℝ) ≤ C*N^2*(δ⁻¹)^2*L^(2*((d : ℝ)-γ-η)) := by
  classical
  obtain ⟨C,R,hC,hB⟩ := large_gap_pair_bound d hd γ hγ η hη hηmax
  refine ⟨C^2,max R 1,sq_nonneg C,?_⟩
  intro L hL δ hδ N hN q1 q2 β1 β2 centers hg1 hg2 F hF
  have hLR : R ≤ L := (le_max_left R 1).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right R 1).trans hL)
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hδN : δ/N ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨div_pos hδ.1 hNp,(div_le_one hNp).mpr (hδ.2.trans hN)⟩
  have ht : (δ/N)⁻¹*L^(-2*γ) = N*(δ⁻¹*L^(-2*γ)) := by
    rw [inv_div,div_eq_mul_inv]
    ring
  obtain ⟨hf1,hb1⟩ := hB L hLR (δ/N) hδN (centers 0) (centers 1) q1 β1 (-1) (fun _ => hg1)
  obtain ⟨hf2,hb2⟩ := hB L hLR (δ/N) hδN (centers 2) (centers 3) q2 β2 (-1) (fun _ => hg2)
  let T := F.image (fun k => ((k 0,k 1),(k 2,k 3)))
  have hi : Function.Injective (fun k : Fin 4 → (Fin d → ℤ) => ((k 0,k 1),(k 2,k 3))) := by
    intro k k' hh
    funext i
    fin_cases i
    · exact congrArg (fun p => p.1.1) hh
    · exact congrArg (fun p => p.1.2) hh
    · exact congrArg (fun p => p.2.1) hh
    · exact congrArg (fun p => p.2.2) hh
  have hcard : T.card = F.card := card_image_of_injective F hi
  have hsub : (T : Set _) ⊆ (atomPairSet L (centers 0) (centers 1) q1 β1 ((δ/N)⁻¹*L^(-2*γ)) (-1)) ×ˢ
      (atomPairSet L (centers 2) (centers 3) q2 β2 ((δ/N)⁻¹*L^(-2*γ)) (-1)) := by
    intro p hp
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hp
    obtain ⟨hm1,hm2,hn,he1,he2⟩ := hF k hk
    constructor
    · exact ⟨hn 0,hn 1,by simpa only [Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_smul,one_smul,sub_eq_add_neg] using hm1,
        by rw [ht]; simpa only [Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_mul,one_mul,sub_eq_add_neg] using he1⟩
    · exact ⟨hn 2,hn 3,by simpa only [Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_smul,one_smul,sub_eq_add_neg] using hm2,
        by rw [ht]; simpa only [Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_mul,one_mul,sub_eq_add_neg] using he2⟩
  have hn := Set.ncard_le_ncard hsub (hf1.prod hf2)
  rw [Set.ncard_coe_finset,Set.ncard_prod,hcard] at hn
  have hnR : (F.card : ℝ) ≤
      ((atomPairSet L (centers 0) (centers 1) q1 β1 ((δ/N)⁻¹*L^(-2*γ)) (-1)).ncard : ℝ)*
      (atomPairSet L (centers 2) (centers 3) q2 β2 ((δ/N)⁻¹*L^(-2*γ)) (-1)).ncard := by exact_mod_cast hn
  have hh := mul_le_mul hb1 hb2 (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hC (inv_nonneg.mpr hδN.1.le)) (Real.rpow_nonneg hLp.le _))
  have hpow : L^((d : ℝ)-γ-η)*L^((d : ℝ)-γ-η) = L^(2*((d : ℝ)-γ-η)) := by
    rw [← Real.rpow_add hLp]
    congr 1 <;> ring
  apply hnR.trans
  calc
    _ ≤ (C*(δ/N)⁻¹*L^((d : ℝ)-γ-η))*(C*(δ/N)⁻¹*L^((d : ℝ)-γ-η)) := hh
    _ = C^2*N^2*(δ⁻¹)^2*(L^((d : ℝ)-γ-η)*L^((d : ℝ)-γ-η)) := by
      rw [inv_div,div_eq_mul_inv]
      ring
    _ = _ := by rw [hpow]

end WaveTurbulence.MoleProp
