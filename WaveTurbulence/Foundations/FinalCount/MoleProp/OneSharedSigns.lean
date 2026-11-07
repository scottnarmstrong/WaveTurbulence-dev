/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.OneSharedTripleCount
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairSignedCount
import Mathlib.Tactic

/-! # Finite orientation normalization for one-shared-label triples

Only finite integer coefficient identities are decided computationally.
Reindexing arbitrary label assignments and source equations is proved
algebraically; no count or source good-configuration estimate is assumed.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

/-- First triple signs are positions 0,1,2; second triple signs are 3,4,5.
The shared label is position zero in the five-label family. -/
def sharedCoefficients (sg : Fin 6 → Bool) (second : Bool) : Fin 5 → ℤ :=
  if second then ![doubleSign (sg 3),0,0,doubleSign (sg 4),doubleSign (sg 5)]
  else ![doubleSign (sg 0),doubleSign (sg 1),doubleSign (sg 2),0,0]

def SharedMixed (sg : Fin 6 → Bool) (second : Bool) : Prop :=
  if second then ¬(sg 3=sg 4 ∧ sg 4=sg 5) else ¬(sg 0=sg 1 ∧ sg 1=sg 2)

instance (sg : Fin 6 → Bool) (second : Bool) : Decidable (SharedMixed sg second) :=
  inferInstanceAs (Decidable (if second then ¬(sg 3=sg 4 ∧ sg 4=sg 5) else ¬(sg 0=sg 1 ∧ sg 1=sg 2)))

def sharedSwapStars (sg : Fin 6 → Bool) : Bool := decide (sg 1≠sg 2 ∧ sg 4=sg 5)

def sharedMode (sg : Fin 6 → Bool) : Fin 3 :=
  if sg 1=sg 2 ∧ sg 4=sg 5 then 2 else if sg 1=sg 2 ∨ sg 4=sg 5 then 1 else 0

def sharedOldSecond (sg : Fin 6 → Bool) (second : Bool) : Bool :=
  if sharedSwapStars sg then !second else second

def sharedHeadSign (sg : Fin 6 → Bool) (second : Bool) : Bool :=
  if sharedOldSecond sg second then sg 3 else sg 0

def sharedFlip (sg : Fin 6 → Bool) (second : Bool) : Bool :=
  decide (sharedHeadSign sg second ≠ (if second then decide (sharedMode sg=1) else decide (sharedMode sg=0)))

def sharedSignFactor (sg : Fin 6 → Bool) (second : Bool) : ℤ :=
  if sharedFlip sg second then -1 else 1

def sharedExternalOne (sg : Fin 6 → Bool) (second : Bool) : Bool :=
  let b := if sharedOldSecond sg second then sg 4 else sg 1
  if sharedFlip sg second then !b else b

def sharedSwapExternal (sg : Fin 6 → Bool) (second : Bool) : Bool :=
  decide (sharedExternalOne sg second ≠ (if second then true else decide (sharedMode sg≠0)))

def sharedPermutation (sg : Fin 6 → Bool) : Fin 5 ≃ Fin 5 :=
  let f : Fin 5 ≃ Fin 5 := if sharedSwapExternal sg false then Equiv.swap 1 2 else Equiv.refl _
  let g : Fin 5 ≃ Fin 5 := if sharedSwapExternal sg true then Equiv.swap 3 4 else Equiv.refl _
  let h : Fin 5 ≃ Fin 5 := if sharedSwapStars sg then (Equiv.swap 1 3).trans (Equiv.swap 2 4) else Equiv.refl _
  (f.trans g).trans h

def sharedCanonicalCoefficients (mode : Fin 3) (second : Bool) : Fin 5 → ℤ :=
  if second then
    if mode=0 then ![-1,0,0,1,-1] else if mode=1 then ![1,0,0,1,-1] else ![-1,0,0,1,1]
  else if mode=0 then ![1,-1,1,0,0] else ![-1,1,1,0,0]

/-- The 36 mixed/mixed sign patterns give precisely the three canonical
coefficient pairs, after a fixed permutation and independent star flips. -/
theorem shared_coefficient_identity : ∀ sg : Fin 6 → Bool,
    SharedMixed sg false → SharedMixed sg true → ∀ second : Bool, ∀ i : Fin 5,
      sharedCanonicalCoefficients (sharedMode sg) second i =
        sharedSignFactor sg second * sharedCoefficients sg (sharedOldSecond sg second) (sharedPermutation sg i) := by
  decide

def sharedParameter {E : Type*} [AddCommGroup E] (sg : Fin 6 → Bool) (second : Bool) (a b : E) : E :=
  sharedSignFactor sg second • (if sharedOldSecond sg second then b else a)

/-- Reindex the actual signed sum in any additive group. -/
theorem shared_sum_normalized {E : Type*} [AddCommGroup E] (sg : Fin 6 → Bool)
    (hA : SharedMixed sg false) (hB : SharedMixed sg true) (second : Bool) (k : Fin 5 → E) :
    (∑ i : Fin 5, sharedCanonicalCoefficients (sharedMode sg) second i • k (sharedPermutation sg i)) =
      sharedSignFactor sg second • (∑ i : Fin 5, sharedCoefficients sg (sharedOldSecond sg second) i • k i) := by
  simp_rw [shared_coefficient_identity sg hA hB second,mul_smul]
  rw [← Finset.smul_sum]
  congr 1
  exact Equiv.sum_comp (sharedPermutation sg) (fun i => sharedCoefficients sg (sharedOldSecond sg second) i • k i)

theorem canonical_shared_sum_one {E : Type*} [AddCommGroup E] (mode : Fin 3) (k : Fin 5 → E) :
    (∑ i : Fin 5, sharedCanonicalCoefficients mode false i • k i) =
      if mode=0 then k 0-k 1+k 2 else k 1+k 2-k 0 := by
  fin_cases mode <;> simp [sharedCanonicalCoefficients,Fin.sum_univ_succ,sub_eq_add_neg]
  all_goals abel

theorem canonical_shared_sum_two {E : Type*} [AddCommGroup E] (mode : Fin 3) (k : Fin 5 → E) :
    (∑ i : Fin 5, sharedCanonicalCoefficients mode true i • k i) =
      if mode=0 then -k 0+k 3-k 4 else if mode=1 then k 0+k 3-k 4 else -k 0+k 3+k 4 := by
  fin_cases mode <;> simp [sharedCanonicalCoefficients,Fin.sum_univ_succ,sub_eq_add_neg]
  all_goals abel

theorem canonical_shared_energy_one {d : ℕ} (mode : Fin 3) (k : Fin 5 → Mom d) :
    (∑ i : Fin 5, sharedCanonicalCoefficients mode false i • ‖k i‖^2) = oneSharedEnergyOne mode k := by
  fin_cases mode <;> simp [sharedCanonicalCoefficients,oneSharedEnergyOne,Fin.sum_univ_succ]
  all_goals ring

theorem canonical_shared_energy_two {d : ℕ} (mode : Fin 3) (k : Fin 5 → Mom d) :
    (∑ i : Fin 5, sharedCanonicalCoefficients mode true i • ‖k i‖^2) = oneSharedEnergyTwo mode k := by
  fin_cases mode <;> simp [sharedCanonicalCoefficients,oneSharedEnergyTwo,Fin.sum_univ_succ]
  all_goals ring

/-- Literal source equations before any orientation normalization. -/
def SignedSharedSource {d : ℕ} (L : ℝ) (sg : Fin 6 → Bool) (a b : Fin d → ℤ)
    (β₁ β₂ τ : ℝ) (centers : Fin 5 → Mom d) (k : Fin 5 → (Fin d → ℤ)) : Prop :=
  (∀ i, CountLemmas.NearLattice L (centers i) (k i)) ∧
    ∀ second : Bool,
      (∑ i : Fin 5, sharedCoefficients sg second i • k i) = (if second then b else a) ∧
      |(∑ i : Fin 5, sharedCoefficients sg second i • ‖latticePoint L (k i)‖^2)-
        (if second then β₂ else β₁)| ≤ τ

/-- Source momentum and energy equations, not estimates, produce the
canonical one-shared-label source family. -/
theorem signedSharedSource_normalized {d : ℕ} (L : ℝ) (sg : Fin 6 → Bool)
    (hA : SharedMixed sg false) (hB : SharedMixed sg true)
    (a b : Fin d → ℤ) (β₁ β₂ τ : ℝ) (centers : Fin 5 → Mom d) (k : Fin 5 → (Fin d → ℤ))
    (hk : SignedSharedSource L sg a b β₁ β₂ τ centers k) :
    OneSharedSource L (sharedMode sg) (sharedParameter sg false a b) (sharedParameter sg true a b)
      (sharedParameter sg false β₁ β₂) (sharedParameter sg true β₁ β₂) τ
      (fun i => centers (sharedPermutation sg i)) (fun i => k (sharedPermutation sg i)) := by
  obtain ⟨hn,hs⟩ := hk
  have hm (second : Bool) := shared_sum_normalized sg hA hB second k
  have he (second : Bool) := shared_sum_normalized sg hA hB second (fun i => ‖latticePoint L (k i)‖^2)
  refine ⟨⟨?_,?_⟩,fun i => hn _,?_,?_⟩
  · have h := hm false
    rw [canonical_shared_sum_one,(hs (sharedOldSecond sg false)).1] at h
    unfold sharedParameter
    split_ifs at h ⊢ <;> exact h
  · have h := hm true
    rw [canonical_shared_sum_two,(hs (sharedOldSecond sg true)).1] at h
    unfold sharedParameter
    split_ifs at h ⊢ <;> exact h
  · rw [← canonical_shared_energy_one,he]
    change |sharedSignFactor sg false • _-sharedSignFactor sg false • _| ≤ τ
    rw [← smul_sub]
    cases hh : sharedFlip sg false <;> simpa [sharedSignFactor,hh,abs_sub_comm] using
      (hs (sharedOldSecond sg false)).2
  · rw [← canonical_shared_energy_two,he]
    change |sharedSignFactor sg true • _-sharedSignFactor sg true • _| ≤ τ
    rw [← smul_sub]
    cases hh : sharedFlip sg true <;> simpa [sharedSignFactor,hh,abs_sub_comm] using
      (hs (sharedOldSecond sg true)).2

/-- Uniform count for all 36 literal mixed/mixed orientations. -/
theorem signed_shared_mixed_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C R : ℝ, 0 < C ∧ ∀ L ≥ R, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (sg : Fin 6 → Bool), SharedMixed sg false → SharedMixed sg true →
    ∀ (a b : Fin d → ℤ) (β₁ β₂ : ℝ) (centers : Fin 5 → Mom d) (N : ℝ), 1 ≤ N →
    ∀ S : Finset (Fin 5 → (Fin d → ℤ)),
      (∀ k ∈ S, SignedSharedSource L sg a b β₁ β₂ (N*(δ⁻¹*L^(-2*γ))) centers k) →
      (S.card : ℝ) ≤ C*N^2*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by
  classical
  obtain ⟨C,R,hC,hB⟩ := one_shared_inflated_window_count_bound d hd γ hγ
  refine ⟨C,R,hC,?_⟩
  intro L hL δ hδ sg hA hBmix a b β₁ β₂ centers N hN S hS
  let f := fun k : Fin 5 → (Fin d → ℤ) => fun i => k (sharedPermutation sg i)
  have hinj : Function.Injective f := by
    intro k k' h
    funext i
    obtain ⟨j,rfl⟩ := (sharedPermutation sg).surjective i
    exact congrFun h j
  have hc : (S.image f).card = S.card := card_image_of_injective _ hinj
  have hb := hB L hL δ hδ N hN (sharedMode sg) (sharedParameter sg false a b) (sharedParameter sg true a b)
    (sharedParameter sg false β₁ β₂) (sharedParameter sg true β₁ β₂)
    (fun i => centers (sharedPermutation sg i)) (S.image f) ?_
  · rw [hc] at hb
    exact hb
  · intro z hz
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hz
    exact signedSharedSource_normalized L sg hA hBmix a b β₁ β₂ _ centers k (hS k hk)

end WaveTurbulence.MoleProp
