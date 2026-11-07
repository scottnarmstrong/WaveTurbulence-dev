/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairLocalCount
import Mathlib.Tactic

/-! # All six directed degree-three patterns of the paired-star count

Literal signed source equations are normalized by reversing every sign
and/or interchanging the two rung labels. Neither operation changes the
number of label assignments or the norm of the external rail difference.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
open CountLemmas

private theorem latticePoint_neg_double {d : ℕ} (L : ℝ) (n : Fin d → ℤ) :
    latticePoint L (-n) = -latticePoint L n := by
  ext i
  simp only [latticePoint,PiLp.neg_apply,Pi.neg_apply,Int.cast_neg]
  ring

def doubleSign (b : Bool) : ℤ := if b then 1 else -1

def doubleRungPermutation (swap : Bool) : Fin 4 ≃ Fin 4 :=
  if swap then Equiv.swap 0 1 else Equiv.refl _

def SignedDoublePairMomentum {E : Type*} [AddCommGroup E] (s t rail : Bool)
    (a b : E) (k : Fin 4 → E) : Prop :=
  doubleSign s • k 0 + doubleSign t • k 1 + doubleSign rail • k 2 = a ∧
    -(doubleSign s • k 0) - doubleSign t • k 1 - doubleSign rail • k 3 = b

noncomputable def signedDoubleEnergyOne {d : ℕ} (s t rail : Bool) (k : Fin 4 → Mom d) : ℝ :=
  doubleSign s * ‖k 0‖^2+doubleSign t * ‖k 1‖^2+doubleSign rail * ‖k 2‖^2

noncomputable def signedDoubleEnergyTwo {d : ℕ} (s t rail : Bool) (k : Fin 4 → Mom d) : ℝ :=
  -doubleSign s * ‖k 0‖^2-doubleSign t * ‖k 1‖^2-doubleSign rail * ‖k 3‖^2

def SignedDoublePairSource {d : ℕ} (L : ℝ) (s t rail : Bool) (a b : Fin d → ℤ)
    (β₁ β₂ τ : ℝ) (centers : Fin 4 → Mom d) (k : Fin 4 → (Fin d → ℤ)) : Prop :=
  SignedDoublePairMomentum s t rail a b k ∧ (∀ i, NearLattice L (centers i) (k i)) ∧
    |signedDoubleEnergyOne s t rail (fun i => latticePoint L (k i))-β₁| ≤ τ ∧
    |signedDoubleEnergyTwo s t rail (fun i => latticePoint L (k i))-β₂| ≤ τ

/-- The source orientation cap excludes exactly the two all-equal
three-incidence patterns. All remaining six patterns normalize literally. -/
theorem signedDoublePair_normalization (s t rail : Bool) (hcap : ¬(s=t ∧ t=rail)) :
    ∃ same reverse swap : Bool,
    ∀ {d : ℕ} (L : ℝ) (a b : Fin d → ℤ) (β₁ β₂ τ : ℝ) (centers : Fin 4 → Mom d)
      (k : Fin 4 → (Fin d → ℤ)),
      SignedDoublePairSource L s t rail a b β₁ β₂ τ centers k →
      DoublePairSource L same (if reverse then -a else a) (if reverse then -b else b)
        (if reverse then -β₁ else β₁) (if reverse then -β₂ else β₂) τ
        (fun i => centers (doubleRungPermutation swap i))
        (fun i => k (doubleRungPermutation swap i)) := by
  refine ⟨decide (s=t),(if s=t then !s else !rail),
    (if s=t then false else decide (s≠rail)),?_⟩
  cases s <;> cases t <;> cases rail
  all_goals try exact False.elim (hcap ⟨rfl,rfl⟩)
  all_goals intro d L a b β₁ β₂ τ centers k hk
  all_goals obtain ⟨hm,hn,h₁,h₂⟩ := hk
  all_goals
    refine ⟨?_,fun i => hn _,?_,?_⟩
    · simp [SignedDoublePairMomentum,doubleSign,doubleRungPermutation,DoublePairMomentum,Equiv.swap_apply_def] at hm ⊢
      constructor
      · rw [← hm.1] <;> abel_nf
      · rw [← hm.2] <;> abel_nf
    · simp [doublePairEnergyOne,doubleRungPermutation,Equiv.swap_apply_def] 
      simp [signedDoubleEnergyOne,doubleSign] at h₁
      first
      | (convert h₁ using 1 <;> congr 1 <;> ring; done)
      | (rw [← abs_neg] at h₁; convert h₁ using 1 <;> congr 1 <;> ring; done)
    · simp [doublePairEnergyTwo,doubleRungPermutation,Equiv.swap_apply_def]
      simp [signedDoubleEnergyTwo,doubleSign] at h₂
      first
      | (convert h₂ using 1 <;> congr 1 <;> ring; done)
      | (rw [← abs_neg] at h₂; convert h₂ using 1 <;> congr 1 <;> ring; done)

/-- Reordering only the two rung labels is injective on all literal
four-label assignments. -/
theorem doubleRungPermutation_injective {E : Type*} (swap : Bool) :
    Function.Injective (fun k : Fin 4 → E => fun i => k (doubleRungPermutation swap i)) := by
  intro k k' h
  funext i
  obtain ⟨j,rfl⟩ := (doubleRungPermutation swap).surjective i
  exact congrFun h j

/-- DH23 basiccount(3), with arbitrary literal degree-three directions.
All charge and energy sign changes are derived by the six-case source
normalization, not supplied as local counting hypotheses. -/
theorem signed_double_pair_local_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (c : ℝ) (hc : 1 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ (s t rail : Bool), ¬(s=t ∧ t=rail) →
    ∀ (a b : Fin d → ℤ) (β₁ β₂ : ℝ) (centers : Fin 4 → Mom d) (P : ℝ),
      (P = 0 ∨ P ∈ Set.Icc L⁻¹ 1) → (0 < P → c⁻¹*P ≤ ‖latticePoint L (a+b)‖) →
    ∀ S : Finset (Fin 4 → (Fin d → ℤ)),
      (∀ k ∈ S, SignedDoublePairSource L s t rail a b β₁ β₂ (δ⁻¹*L^(-2*γ)) centers k) →
      (S.card : ℝ) ≤ C*δ⁻¹*L^(2*((d : ℝ)-γ))*(min (Real.log L^2) (1+δ*L^(2*γ)*P))⁻¹ := by
  classical
  obtain ⟨C,hC,hB⟩ := double_pair_local_count_bound d hd γ hγ c hc
  refine ⟨C,hC,?_⟩
  intro δ hδ
  obtain ⟨R,hR⟩ := hB δ hδ
  refine ⟨R,?_⟩
  intro L hL s t rail hcap a b β₁ β₂ centers P hP hgap S hS
  obtain ⟨same,reverse,swap,hnorm⟩ := signedDoublePair_normalization s t rail hcap
  let f := fun k : Fin 4 → (Fin d → ℤ) => fun i => k (doubleRungPermutation swap i)
  have hcard : (S.image f).card = S.card := card_image_of_injective _ (doubleRungPermutation_injective swap)
  have hg : 0 < P → c⁻¹*P ≤ ‖latticePoint L ((if reverse then -a else a)+(if reverse then -b else b))‖ := by
    cases reverse
    · exact hgap
    · simpa only [ite_true,← neg_add,latticePoint_neg_double,norm_neg] using hgap
  have hb := hR L hL same (if reverse then -a else a) (if reverse then -b else b)
    (if reverse then -β₁ else β₁) (if reverse then -β₂ else β₂)
    (fun i => centers (doubleRungPermutation swap i)) P hP hg (S.image f) ?_
  · rw [hcard] at hb
    exact hb
  · intro z hz
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hz
    exact hnorm L a b β₁ β₂ _ centers k (hS k hk)

end WaveTurbulence.MoleProp
