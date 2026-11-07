/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.OneSharedSameSign
import Mathlib.Tactic

/-! # First mixed triple followed by a conditional positive pair

The remaining pair's fixed momentum and energy center may be arbitrary
functions of the first three labels. Actual equations, not fiber counts,
are the hypotheses of this local counting helper.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
open CountLemmas

def TriplePositiveSource {d : ℕ} (L : ℝ) (sg : Fin 3 → Bool) (a : Fin d → ℤ)
    (β τ : ℝ) (centers : Fin 5 → Mom d)
    (nk : (Fin 3 → (Fin d → ℤ)) → (Fin d → ℤ)) (bp : (Fin 3 → (Fin d → ℤ)) → ℝ)
    (k : Fin 5 → (Fin d → ℤ)) : Prop :=
  (∀ i, NearLattice L (centers i) (k i)) ∧
    (∑ i : Fin 3, doubleSign (sg i) • sharedFirstProfile k i)=a ∧
    |(∑ i : Fin 3, doubleSign (sg i) • ‖latticePoint L (sharedFirstProfile k i)‖^2)-β| ≤ τ ∧
    k 3+k 4=nk (sharedFirstProfile k) ∧
    |‖latticePoint L (k 3)‖^2+‖latticePoint L (k 4)‖^2-bp (sharedFirstProfile k)| ≤ τ

theorem triple_positive_pair_fiber_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ≤ 1)
    {L δ : ℝ} (hL : 1 ≤ L) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1)
    (sg : Fin 3 → Bool) (a : Fin d → ℤ) (β : ℝ) (centers : Fin 5 → Mom d)
    (nk : (Fin 3 → (Fin d → ℤ)) → (Fin d → ℤ)) (bp : (Fin 3 → (Fin d → ℤ)) → ℝ)
    (S : Finset (Fin 5 → (Fin d → ℤ)))
    (hS : ∀ k ∈ S, TriplePositiveSource L sg a β (δ⁻¹*L^(-2*γ)) centers nk bp k)
    (q : Fin 3 → (Fin d → ℤ)) :
    ((S.filter fun k => sharedFirstProfile k=q).card : ℝ) ≤
      (3^(d-2)*(2*(6*Real.pi+1284002)))*δ⁻¹*L^((d : ℝ)-γ-min γ (1-γ)) := by
  classical
  have hLp : 0 < L := zero_lt_one.trans_le hL
  let F := S.filter fun k => sharedFirstProfile k=q
  let T := F.image (fun k => (k 3,k 4))
  have hcard : T.card=F.card := card_image_of_injOn (shared_first_fiber_pair_injOn S q)
  have hf := finite_atomPairSet hLp (centers 3) (centers 4) (nk q) (bp q) (δ⁻¹*L^(-2*γ)) 1
  have hsub : (T : Set ((Fin d → ℤ) × (Fin d → ℤ))) ⊆
      atomPairSet L (centers 3) (centers 4) (nk q) (bp q) (δ⁻¹*L^(-2*γ)) 1 := by
    intro z hz
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hz
    obtain ⟨hk,hkq⟩ := mem_filter.mp hk
    obtain ⟨hn,_hm,_he,hpm,hpe⟩ := hS k hk
    rw [hkq] at hpm hpe
    exact ⟨hn 3,hn 4,by simpa using hpm,by simpa using hpe⟩
  have hn : T.card ≤ (atomPairSet L (centers 3) (centers 4) (nk q) (bp q) (δ⁻¹*L^(-2*γ)) 1).ncard := by
    simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub hf
  have hnR : (T.card : ℝ) ≤ (atomPairSet L (centers 3) (centers 4) (nk q) (bp q) (δ⁻¹*L^(-2*γ)) 1).ncard := by exact_mod_cast hn
  rw [hcard] at hnR
  exact hnR.trans (positive_pair_sharp_bound (by omega : 2 ≤ d) hL hδ hγ (centers 3) (centers 4) (nk q) (bp q))

theorem triple_positive_pair_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C R : ℝ, 0 ≤ C ∧ ∀ L ≥ R, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (sg : Fin 3 → Bool), ¬(sg 0=sg 1 ∧ sg 1=sg 2) →
    ∀ (a : Fin d → ℤ) (β : ℝ) (centers : Fin 5 → Mom d)
      (nk : (Fin 3 → (Fin d → ℤ)) → (Fin d → ℤ)) (bp : (Fin 3 → (Fin d → ℤ)) → ℝ)
      (S : Finset (Fin 5 → (Fin d → ℤ))),
      (∀ k ∈ S, TriplePositiveSource L sg a β (δ⁻¹*L^(-2*γ)) centers nk bp k) →
      (S.card : ℝ) ≤ C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by
  classical
  obtain ⟨Ct,R,hCt,hB⟩ := literal_signed_triple_count_bound d hd γ hγ
  let Cp : ℝ := 3^(d-2)*(2*(6*Real.pi+1284002))
  have hCp : 0 ≤ Cp := by dsimp only [Cp]; positivity
  refine ⟨Ct*Cp,max R 1,mul_nonneg hCt hCp,?_⟩
  intro L hL δ hδ sg hsg a β centers nk bp S hS
  have hL1 : 1 ≤ L := (le_max_right R 1).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  let F := S.image sharedFirstProfile
  have hFirst : ∀ k ∈ F, (∀ i, NearLattice L (sharedFirstProfile centers i) (k i)) ∧
      (∑ i : Fin 3, doubleSign (sg i) • k i)=a ∧
      |(∑ i : Fin 3, doubleSign (sg i) • ‖latticePoint L (k i)‖^2)-β| ≤ δ⁻¹*L^(-2*γ) := by
    intro z hz
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hz
    obtain ⟨hn,hm,he,_hpm,_hpe⟩ := hS k hk
    exact ⟨fun i => hn _,hm,he⟩
  have hF := hB L ((le_max_left R 1).trans hL) δ hδ sg hsg a β (sharedFirstProfile centers) F hFirst
  have hc : S.card=∑ q ∈ F, (S.filter fun k => sharedFirstProfile k=q).card :=
    card_eq_sum_card_fiberwise (fun k hk => mem_image.mpr ⟨k,hk,rfl⟩)
  have hcR : (S.card : ℝ)=∑ q ∈ F, ((S.filter fun k => sharedFirstProfile k=q).card : ℝ) := by exact_mod_cast hc
  rw [hcR]
  calc
    _ ≤ ∑ _q ∈ F, Cp*δ⁻¹*L^((d : ℝ)-γ-min γ (1-γ)) := by
      apply sum_le_sum
      intro q _hq
      exact triple_positive_pair_fiber_bound d hd γ hγ.2.le hL1 hδ sg a β centers nk bp S hS q
    _ = (F.card : ℝ)*(Cp*δ⁻¹*L^((d : ℝ)-γ-min γ (1-γ))) := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ (Ct*δ⁻¹*L^(2*((d : ℝ)-γ)))*(Cp*δ⁻¹*L^((d : ℝ)-γ-min γ (1-γ))) :=
      mul_le_mul_of_nonneg_right hF
        (mul_nonneg (mul_nonneg hCp (inv_nonneg.mpr hδ.1.le)) (Real.rpow_nonneg hLp.le _))
    _ = _ := by
      rw [show (3*((d : ℝ)-γ)-min γ (1-γ))=2*((d : ℝ)-γ)+((d : ℝ)-γ-min γ (1-γ)) by ring,Real.rpow_add hLp]
      ring

end WaveTurbulence.MoleProp
