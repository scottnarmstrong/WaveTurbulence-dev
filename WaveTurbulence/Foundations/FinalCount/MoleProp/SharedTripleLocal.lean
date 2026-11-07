/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.OneSharedSigns
public import WaveTurbulence.Foundations.FinalCount.MoleProp.SharpPositivePair
import Mathlib.Tactic

/-! # Literal signed mixed-triple counts independent of a graph carrier

This is the first-triple ingredient for the easy all-same virtual-star
branch. Its orientation normalization is a finite coefficient identity.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
open CountLemmas

def sharedTripleMajority (sg : Fin 3 → Bool) : Bool := if sg 0=sg 1 then sg 0 else sg 2

def sharedTripleMinority (sg : Fin 3 → Bool) : Fin 3 :=
  if sg 0≠sharedTripleMajority sg then 0 else if sg 1≠sharedTripleMajority sg then 1 else 2

def sharedTriplePermutation (sg : Fin 3 → Bool) : Fin 3 ≃ Fin 3 :=
  Equiv.swap 1 (sharedTripleMinority sg)

def sharedTripleFactor (sg : Fin 3 → Bool) : ℤ := if sharedTripleMajority sg then 1 else -1

theorem sharedTriple_coefficient_identity : ∀ sg : Fin 3 → Bool,
    ¬(sg 0=sg 1 ∧ sg 1=sg 2) → ∀ i : Fin 3,
      (![1,-1,1] : Fin 3 → ℤ) i = sharedTripleFactor sg * doubleSign (sg (sharedTriplePermutation sg i)) := by
  decide

theorem sharedTriple_sum_normalized {E : Type*} [AddCommGroup E] (sg : Fin 3 → Bool)
    (hsg : ¬(sg 0=sg 1 ∧ sg 1=sg 2)) (k : Fin 3 → E) :
    k (sharedTriplePermutation sg 0)-k (sharedTriplePermutation sg 1)+k (sharedTriplePermutation sg 2) =
      sharedTripleFactor sg • (∑ i : Fin 3, doubleSign (sg i) • k i) := by
  have he : (∑ i : Fin 3, (![1,-1,1] : Fin 3 → ℤ) i • k (sharedTriplePermutation sg i)) =
      sharedTripleFactor sg • (∑ i : Fin 3, doubleSign (sg i) • k i) := by
    simp_rw [sharedTriple_coefficient_identity sg hsg,mul_smul]
    rw [← Finset.smul_sum]
    congr 1
    exact Equiv.sum_comp (sharedTriplePermutation sg) (fun i => doubleSign (sg i) • k i)
  simpa [Fin.sum_univ_three,sub_eq_add_neg] using he

theorem literal_signed_triple_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C R : ℝ, 0 ≤ C ∧ ∀ L ≥ R, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (sg : Fin 3 → Bool), ¬(sg 0=sg 1 ∧ sg 1=sg 2) →
    ∀ (a : Fin d → ℤ) (β : ℝ) (centers : Fin 3 → Mom d) (S : Finset (Fin 3 → (Fin d → ℤ))),
      (∀ k ∈ S, (∀ i, NearLattice L (centers i) (k i)) ∧
        (∑ i : Fin 3, doubleSign (sg i) • k i)=a ∧
        |(∑ i : Fin 3, doubleSign (sg i) • ‖latticePoint L (k i)‖^2)-β| ≤ δ⁻¹*L^(-2*γ)) →
      (S.card : ℝ) ≤ C*δ⁻¹*L^(2*((d : ℝ)-γ)) := by
  classical
  obtain ⟨C,R,hB⟩ := atomTriple_bound d hd γ hγ
  refine ⟨max C 0,max R 1,le_max_right _ _,?_⟩
  intro L hL δ hδ sg hsg a β centers S hS
  have hL0 : 0 ≤ L := zero_le_one.trans ((le_max_right R 1).trans hL)
  let e := sharedTriplePermutation sg
  let f := fun k : Fin 3 → (Fin d → ℤ) => (k (e 0),k (e 1),k (e 2))
  have hinj : Function.Injective f := by
    intro k k' he
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    fin_cases j
    · exact congrArg Prod.fst he
    · exact congrArg (fun z => z.2.1) he
    · exact congrArg (fun z => z.2.2) he
  let T := S.image f
  have hcard : T.card = S.card := card_image_of_injective _ hinj
  obtain ⟨hf,hb⟩ := hB L ((le_max_left R 1).trans hL) δ hδ
    (sharedTripleFactor sg • β) (sharedTripleFactor sg • a) (centers (e 0)) (centers (e 1)) (centers (e 2))
  have hsub : (T : Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))) ⊆
      atomTripleSet L (centers (e 0)) (centers (e 1)) (centers (e 2)) (sharedTripleFactor sg • a)
        (sharedTripleFactor sg • β) (δ⁻¹*L^(-2*γ)) := by
    intro z hz
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hz
    obtain ⟨hn,hm,he⟩ := hS k hk
    refine ⟨hn _,hn _,hn _,?_,?_⟩
    · have h := sharedTriple_sum_normalized sg hsg k
      rw [hm] at h
      exact h
    · have h := sharedTriple_sum_normalized sg hsg (fun i => ‖latticePoint L (k i)‖^2)
      change |‖latticePoint L (k (e 0))‖^2-‖latticePoint L (k (e 1))‖^2+
        ‖latticePoint L (k (e 2))‖^2-sharedTripleFactor sg • β| ≤ _
      rw [h,← smul_sub]
      cases hh : sharedTripleMajority sg <;>
        simpa [sharedTripleFactor,hh,abs_sub_comm] using he
  have hn : T.card ≤ (atomTripleSet L (centers (e 0)) (centers (e 1)) (centers (e 2))
      (sharedTripleFactor sg • a) (sharedTripleFactor sg • β) (δ⁻¹*L^(-2*γ))).ncard := by
    simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub hf
  have hnR : (T.card : ℝ) ≤ (atomTripleSet L (centers (e 0)) (centers (e 1)) (centers (e 2))
      (sharedTripleFactor sg • a) (sharedTripleFactor sg • β) (δ⁻¹*L^(-2*γ))).ncard := by exact_mod_cast hn
  rw [hcard] at hnR
  exact hnR.trans (hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left C 0) (inv_nonneg.mpr hδ.1.le)) (Real.rpow_nonneg hL0 _)))

end WaveTurbulence.MoleProp
