/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.UnbalancedDoubleTriple
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairFiveSignedCount
import Mathlib.Tactic

/-! # Literal virtual quad signs without a balance premise

The first triple is mixed. The second shares its first two labels with
opposite coefficients and has two arbitrary remaining signs. Only the
opposite-remaining-sign branches are normalized in this module.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

def doubleSharedCoefficients (sg : Fin 5 → Bool) (second : Bool) : Fin 5 → ℤ :=
  if second then ![-doubleSign (sg 0),-doubleSign (sg 1),0,doubleSign (sg 3),doubleSign (sg 4)]
  else ![doubleSign (sg 0),doubleSign (sg 1),doubleSign (sg 2),0,0]

def SignedDoubleSharedSource {d : ℕ} (L : ℝ) (sg : Fin 5 → Bool) (a b : Fin d → ℤ)
    (β₁ β₂ τ : ℝ) (centers : Fin 5 → Mom d) (k : Fin 5 → (Fin d → ℤ)) : Prop :=
  (∀ i, CountLemmas.NearLattice L (centers i) (k i)) ∧
    ∀ second : Bool,
      (∑ i : Fin 5, doubleSharedCoefficients sg second i • k i)=(if second then b else a) ∧
      |(∑ i : Fin 5, doubleSharedCoefficients sg second i • ‖latticePoint L (k i)‖^2)-
        (if second then β₂ else β₁)| ≤ τ

def doubleSharedBalancedPermutation (sg : Fin 5 → Bool) : Fin 5 ≃ Fin 5 :=
  if sg 3=sg 2 then Equiv.swap 3 4 else Equiv.refl _

def balancedFiveCoefficients (sg : Fin 5 → Bool) (second : Bool) : Fin 5 → ℤ :=
  if second then ![-doubleSign (sg 0),-doubleSign (sg 1),0,-doubleSign (sg 2),
    doubleSign (doubleExtraSign (sg 0) (sg 1) (sg 2))]
  else ![doubleSign (sg 0),doubleSign (sg 1),doubleSign (sg 2),0,0]

theorem doubleShared_balanced_coefficient_identity : ∀ sg : Fin 5 → Bool,
    sg 0≠sg 1 → sg 3≠sg 4 → ∀ second : Bool, ∀ i : Fin 5,
      balancedFiveCoefficients sg second i=
        doubleSharedCoefficients sg second (doubleSharedBalancedPermutation sg i) := by decide

def doubleSharedUnbalancedPermutation (sg : Fin 5 → Bool) : Fin 5 ≃ Fin 5 :=
  if sg 3=sg 0 then Equiv.refl _ else Equiv.swap 3 4

def unbalancedFiveCoefficients (second : Bool) : Fin 5 → ℤ :=
  if second then ![-1,-1,0,1,-1] else ![1,1,-1,0,0]

theorem doubleShared_unbalanced_coefficient_identity : ∀ sg : Fin 5 → Bool,
    ¬(sg 0=sg 1 ∧ sg 1=sg 2) → sg 0=sg 1 → sg 3≠sg 4 → ∀ second : Bool, ∀ i : Fin 5,
      unbalancedFiveCoefficients second i=doubleSign (sg 0)*
        doubleSharedCoefficients sg second (doubleSharedUnbalancedPermutation sg i) := by decide

private theorem scaled_reindex_sum {E : Type*} [AddCommGroup E]
    (p : Fin 5 ≃ Fin 5) (σ : ℤ) (a b : Fin 5 → ℤ)
    (h : ∀ i, a i=σ*b (p i)) (k : Fin 5 → E) :
    (∑ i : Fin 5, a i • k (p i))=σ • (∑ i : Fin 5, b i • k i) := by
  simp_rw [h,mul_smul]
  rw [← Finset.smul_sum]
  congr 1
  exact Equiv.sum_comp p (fun i => b i • k i)

/-- Mixed shared signs and opposite remaining signs give the already
proved balanced five-label system by choosing the remaining-label order. -/
theorem doubleSharedSource_to_balanced {d : ℕ} (L : ℝ) (sg : Fin 5 → Bool)
    (hshared : sg 0≠sg 1) (hpair : sg 3≠sg 4)
    (a b : Fin d → ℤ) (β₁ β₂ τ : ℝ) (centers : Fin 5 → Mom d) (k : Fin 5 → (Fin d → ℤ))
    (hk : SignedDoubleSharedSource L sg a b β₁ β₂ τ centers k) :
    SignedDoubleFiveSource L (sg 0) (sg 1) (sg 2) a b β₁ β₂ τ
      (fun i => centers (doubleSharedBalancedPermutation sg i))
      (fun i => k (doubleSharedBalancedPermutation sg i)) := by
  obtain ⟨hn,hs⟩ := hk
  have hm (second : Bool) := scaled_reindex_sum (doubleSharedBalancedPermutation sg) 1
    (balancedFiveCoefficients sg second) (doubleSharedCoefficients sg second)
    (fun i => by simpa only [one_mul] using doubleShared_balanced_coefficient_identity sg hshared hpair second i) k
  have he (second : Bool) := scaled_reindex_sum (doubleSharedBalancedPermutation sg) 1
    (balancedFiveCoefficients sg second) (doubleSharedCoefficients sg second)
    (fun i => by simpa only [one_mul] using doubleShared_balanced_coefficient_identity sg hshared hpair second i)
    (fun i => ‖latticePoint L (k i)‖^2)
  simp only [one_smul] at hm he
  refine ⟨⟨?_,?_⟩,fun i => hn _,?_,?_⟩
  · have h := (hm false).trans (hs false).1
    simpa [balancedFiveCoefficients,Fin.sum_univ_succ,sub_eq_add_neg,add_assoc] using h
  · have h := (hm true).trans (hs true).1
    simpa [balancedFiveCoefficients,Fin.sum_univ_succ,sub_eq_add_neg,add_assoc] using h
  · have h := (hs false).2
    rw [← he false] at h
    simpa [balancedFiveCoefficients,Fin.sum_univ_succ,signedDoubleFiveEnergyOne,zsmul_eq_mul,add_assoc] using h
  · have h := (hs true).2
    rw [← he true] at h
    simpa [balancedFiveCoefficients,Fin.sum_univ_succ,signedDoubleFiveEnergyTwo,zsmul_eq_mul,sub_eq_add_neg,add_assoc] using h

/-- Equal shared signs and opposite remaining signs produce the virtual
unbalanced quad. Balance is not introduced as an extra source premise. -/
theorem doubleSharedSource_to_unbalanced {d : ℕ} (L : ℝ) (sg : Fin 5 → Bool)
    (hfirst : ¬(sg 0=sg 1 ∧ sg 1=sg 2)) (hshared : sg 0=sg 1) (hpair : sg 3≠sg 4)
    (a b : Fin d → ℤ) (β₁ β₂ τ : ℝ) (centers : Fin 5 → Mom d) (k : Fin 5 → (Fin d → ℤ))
    (hk : SignedDoubleSharedSource L sg a b β₁ β₂ τ centers k) :
    UnbalancedSource L (doubleSign (sg 0) • a) (doubleSign (sg 0) • b)
      (doubleSign (sg 0) • β₁) (doubleSign (sg 0) • β₂) τ
      (fun i => centers (doubleSharedUnbalancedPermutation sg i))
      (fun i => k (doubleSharedUnbalancedPermutation sg i)) := by
  obtain ⟨hn,hs⟩ := hk
  have hm (second : Bool) := scaled_reindex_sum (doubleSharedUnbalancedPermutation sg) (doubleSign (sg 0))
    (unbalancedFiveCoefficients second) (doubleSharedCoefficients sg second)
    (doubleShared_unbalanced_coefficient_identity sg hfirst hshared hpair second) k
  have he (second : Bool) := scaled_reindex_sum (doubleSharedUnbalancedPermutation sg) (doubleSign (sg 0))
    (unbalancedFiveCoefficients second) (doubleSharedCoefficients sg second)
    (doubleShared_unbalanced_coefficient_identity sg hfirst hshared hpair second)
    (fun i => ‖latticePoint L (k i)‖^2)
  refine ⟨⟨?_,?_⟩,fun i => hn _,?_,?_⟩
  · have h := hm false
    rw [(hs false).1] at h
    simpa [unbalancedFiveCoefficients,Fin.sum_univ_succ,sub_eq_add_neg,add_assoc] using h
  · have h := hm true
    rw [(hs true).1] at h
    simpa [unbalancedFiveCoefficients,Fin.sum_univ_succ,sub_eq_add_neg,add_assoc] using h
  · have h := he false
    have hh : unbalancedEnergyOne (fun i => latticePoint L (k (doubleSharedUnbalancedPermutation sg i)))=
        doubleSign (sg 0) • ∑ i : Fin 5, doubleSharedCoefficients sg false i • ‖latticePoint L (k i)‖^2 := by
      simpa [unbalancedEnergyOne,unbalancedFiveCoefficients,Fin.sum_univ_succ,sub_eq_add_neg,add_assoc] using h
    rw [hh,← smul_sub]
    cases hx : sg 0 <;> simpa [doubleSign,hx,abs_sub_comm] using (hs false).2
  · have h := he true
    have hh : unbalancedEnergyTwo (fun i => latticePoint L (k (doubleSharedUnbalancedPermutation sg i)))=
        doubleSign (sg 0) • ∑ i : Fin 5, doubleSharedCoefficients sg true i • ‖latticePoint L (k i)‖^2 := by
      simpa [unbalancedEnergyTwo,unbalancedFiveCoefficients,Fin.sum_univ_succ,sub_eq_add_neg,add_assoc] using h
    rw [hh,← smul_sub]
    cases hx : sg 0 <;> simpa [doubleSign,hx,abs_sub_comm] using (hs true).2

end WaveTurbulence.MoleProp
