/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairFiveCount
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairSignedCount
import Mathlib.Tactic

/-! # All six directed paired three/four-valent patterns

Literal signed source equations are normalized by reversing every sign
and/or interchanging the two rung labels. Neither operation changes the
number of label assignments or the norm of the external rail difference.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
open CountLemmas

def fiveRungPermutation (swap : Bool) : Fin 5 ≃ Fin 5 :=
  if swap then Equiv.swap 0 1 else Equiv.refl _

/-- The fourth atom is balanced: the fifth incidence sign is forced by
its two rung signs and its other rail sign. -/
def doubleExtraSign (s t rail : Bool) : Bool := if s=t then s else rail

def SignedDoubleFiveMomentum {E : Type*} [AddCommGroup E] (s t rail : Bool)
    (a b : E) (k : Fin 5 → E) : Prop :=
  doubleSign s • k 0 + doubleSign t • k 1 + doubleSign rail • k 2 = a ∧
    -(doubleSign s • k 0) - doubleSign t • k 1 - doubleSign rail • k 3 +
      doubleSign (doubleExtraSign s t rail) • k 4 = b

noncomputable def signedDoubleFiveEnergyOne {d : ℕ} (s t rail : Bool) (k : Fin 5 → Mom d) : ℝ :=
  doubleSign s * ‖k 0‖^2+doubleSign t * ‖k 1‖^2+doubleSign rail * ‖k 2‖^2

noncomputable def signedDoubleFiveEnergyTwo {d : ℕ} (s t rail : Bool) (k : Fin 5 → Mom d) : ℝ :=
  -doubleSign s * ‖k 0‖^2-doubleSign t * ‖k 1‖^2-doubleSign rail * ‖k 3‖^2+
    doubleSign (doubleExtraSign s t rail) * ‖k 4‖^2

def SignedDoubleFiveSource {d : ℕ} (L : ℝ) (s t rail : Bool) (a b : Fin d → ℤ)
    (β₁ β₂ τ : ℝ) (centers : Fin 5 → Mom d) (k : Fin 5 → (Fin d → ℤ)) : Prop :=
  SignedDoubleFiveMomentum s t rail a b k ∧ (∀ i, NearLattice L (centers i) (k i)) ∧
    |signedDoubleFiveEnergyOne s t rail (fun i => latticePoint L (k i))-β₁| ≤ τ ∧
    |signedDoubleFiveEnergyTwo s t rail (fun i => latticePoint L (k i))-β₂| ≤ τ

/-- The source orientation cap excludes exactly the two all-equal
three-incidence patterns. All remaining six patterns normalize literally. -/
theorem signedDoubleFive_normalization (s t rail : Bool) (hcap : ¬(s=t ∧ t=rail)) :
    ∃ same reverse swap : Bool,
    ∀ {d : ℕ} (L : ℝ) (a b : Fin d → ℤ) (β₁ β₂ τ : ℝ) (centers : Fin 5 → Mom d)
      (k : Fin 5 → (Fin d → ℤ)),
      SignedDoubleFiveSource L s t rail a b β₁ β₂ τ centers k →
      DoubleFiveSource L same (if reverse then -a else a) (if reverse then -b else b)
        (if reverse then -β₁ else β₁) (if reverse then -β₂ else β₂) τ
        (fun i => centers (fiveRungPermutation swap i))
        (fun i => k (fiveRungPermutation swap i)) := by
  refine ⟨decide (s=t),(if s=t then !s else !rail),
    (if s=t then false else decide (s≠rail)),?_⟩
  cases s <;> cases t <;> cases rail
  all_goals try exact False.elim (hcap ⟨rfl,rfl⟩)
  all_goals intro d L a b β₁ β₂ τ centers k hk
  all_goals obtain ⟨hm,hn,h₁,h₂⟩ := hk
  all_goals
    refine ⟨?_,fun i => hn _,?_,?_⟩
    · simp [SignedDoubleFiveMomentum,doubleSign,fiveRungPermutation,DoubleFiveMomentum,doubleExtraSign,Equiv.swap_apply_def] at hm ⊢
      constructor
      · rw [← hm.1] <;> abel_nf
      · rw [← hm.2] <;> abel_nf
    · simp [doubleFiveEnergyOne,fiveRungPermutation,Equiv.swap_apply_def] 
      simp [signedDoubleFiveEnergyOne,doubleSign,doubleExtraSign] at h₁
      first
      | (convert h₁ using 1 <;> congr 1 <;> ring; done)
      | (rw [← abs_neg] at h₁; convert h₁ using 1 <;> congr 1 <;> ring; done)
    · simp [doubleFiveEnergyTwo,fiveRungPermutation,Equiv.swap_apply_def]
      simp [signedDoubleFiveEnergyTwo,doubleSign,doubleExtraSign] at h₂
      first
      | (convert h₂ using 1 <;> congr 1 <;> ring; done)
      | (rw [← abs_neg] at h₂; convert h₂ using 1 <;> congr 1 <;> ring; done)

/-- Reordering only the two rung labels is injective on all literal
four-label assignments. -/
theorem fiveRungPermutation_injective {E : Type*} (swap : Bool) :
    Function.Injective (fun k : Fin 5 → E => fun i => k (fiveRungPermutation swap i)) := by
  intro k k' h
  funext i
  obtain ⟨j,rfl⟩ := (fiveRungPermutation swap).surjective i
  exact congrFun h j

/-- DH23 basiccount(4), all six balanced paired-star orientation patterns,
with a genuine five-label source system and arbitrary fixed charges. -/
theorem signed_double_five_local_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C R : ℝ, 0 < C ∧ ∀ L ≥ R, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (s t rail : Bool), ¬(s=t ∧ t=rail) →
    ∀ (a b : Fin d → ℤ) (β₁ β₂ : ℝ) (centers : Fin 5 → Mom d),
    ∀ S : Finset (Fin 5 → (Fin d → ℤ)),
      (∀ k ∈ S, SignedDoubleFiveSource L s t rail a b β₁ β₂ (δ⁻¹*L^(-2*γ)) centers k) →
      (S.card : ℝ) ≤ C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by
  classical
  obtain ⟨C,R,hC,hB⟩ := double_five_local_count_bound d hd γ hγ
  refine ⟨C,R,hC,?_⟩
  intro L hL δ hδ s t rail hcap a b β₁ β₂ centers S hS
  obtain ⟨same,reverse,swap,hnorm⟩ := signedDoubleFive_normalization s t rail hcap
  let f := fun k : Fin 5 → (Fin d → ℤ) => fun i => k (fiveRungPermutation swap i)
  have hcard : (S.image f).card = S.card := card_image_of_injective _ (fiveRungPermutation_injective swap)
  have hb := hB L hL δ hδ same (if reverse then -a else a) (if reverse then -b else b)
    (if reverse then -β₁ else β₁) (if reverse then -β₂ else β₂)
    (fun i => centers (fiveRungPermutation swap i)) (S.image f) ?_
  · rw [hcard] at hb
    exact hb
  · intro z hz
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hz
    exact hnorm L a b β₁ β₂ _ centers k (hS k hk)

end WaveTurbulence.MoleProp
