/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairAlgebra
import Mathlib.Tactic

/-! # Exact five-label coordinates for DH23 basiccount(4)

A three-valent atom and a four-valent atom share a double bond. The
combined energy is a coupled-triple constraint, with its exact minus sign.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

def doubleFiveLabels {E : Type*} [AddCommGroup E] (same : Bool) (a b x y z : E) : Fin 5 → E :=
  if same then ![x+a,y+a,x+y+a,x+y-z+a,z+(a+b)]
  else ![y+a,x+y+a,x+a,x+z+a,z+(a+b)]

def DoubleFiveMomentum {E : Type*} [AddCommGroup E] (same : Bool) (a b : E) (k : Fin 5 → E) : Prop :=
  if same then k 0+k 1-k 2=a ∧ -k 0-k 1+k 3+k 4=b
  else k 0-k 1+k 2=a ∧ -k 0+k 1-k 3+k 4=b

def doubleFiveCoordinates {E : Type*} [AddCommGroup E] (same : Bool) (a b : E)
    (k : Fin 5 → E) : E × E × E :=
  (if same then k 0-a else k 2-a,if same then k 1-a else k 0-a,k 4-(a+b))

theorem doubleFiveLabels_reconstruct {E : Type*} [AddCommGroup E] (same : Bool)
    (a b : E) (k : Fin 5 → E) (hk : DoubleFiveMomentum same a b k) :
    k = doubleFiveLabels same a b (doubleFiveCoordinates same a b k).1
      (doubleFiveCoordinates same a b k).2.1 (doubleFiveCoordinates same a b k).2.2 := by
  cases same
  · change k 0-k 1+k 2=a ∧ -k 0+k 1-k 3+k 4=b at hk
    have h1 : k 1=k 0+k 2-a := by rw [← hk.1]; abel
    have h3 : k 3=k 2+k 4-a-b := by rw [← hk.1,← hk.2]; abel
    funext i
    fin_cases i <;> simp [doubleFiveLabels,doubleFiveCoordinates,h1,h3]
    all_goals abel
  · change k 0+k 1-k 2=a ∧ -k 0-k 1+k 3+k 4=b at hk
    have h2 : k 2=k 0+k 1-a := by rw [← hk.1]; abel
    have h3 : k 3=k 0+k 1-k 4+b := by rw [← hk.2]; abel
    funext i
    fin_cases i <;> simp [doubleFiveLabels,doubleFiveCoordinates,h2,h3]
    all_goals abel

noncomputable def doubleFiveEnergyOne {d : ℕ} (same : Bool) (k : Fin 5 → Mom d) : ℝ :=
  if same then ‖k 0‖^2+‖k 1‖^2-‖k 2‖^2 else ‖k 0‖^2-‖k 1‖^2+‖k 2‖^2

noncomputable def doubleFiveEnergyTwo {d : ℕ} (same : Bool) (k : Fin 5 → Mom d) : ℝ :=
  if same then -‖k 0‖^2-‖k 1‖^2+‖k 3‖^2+‖k 4‖^2
  else -‖k 0‖^2+‖k 1‖^2-‖k 3‖^2+‖k 4‖^2

theorem doubleFive_first_energy {d : ℕ} (same : Bool) (a b x y z : Mom d) :
    doubleFiveEnergyOne same (doubleFiveLabels same a b x y z) = ‖a‖^2-2*inner ℝ x y := by
  cases same <;> simp [doubleFiveEnergyOne,doubleFiveLabels,norm_add_sq_real,inner_add_left]
  all_goals simp only [real_inner_comm y x,real_inner_comm a x,real_inner_comm a y]
  all_goals ring

/-- The minus sign follows from subtracting the two shared-rung energies.
It is absorbed into the energy center of the final counting strip. -/
theorem doubleFive_combined_energy {d : ℕ} (same : Bool) (a b x y z : Mom d) :
    doubleFiveEnergyOne same (doubleFiveLabels same a b x y z)+
      doubleFiveEnergyTwo same (doubleFiveLabels same a b x y z) =
      ‖a+b‖^2-2*inner ℝ (if same then x+y-b-z else x-b) z := by
  cases same <;> simp [doubleFiveEnergyOne,doubleFiveEnergyTwo,doubleFiveLabels,
    norm_add_sq_real,norm_sub_sq_real,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right]
  all_goals simp only [real_inner_comm a x,real_inner_comm a y,real_inner_comm a z,
    real_inner_comm b x,real_inner_comm b y,real_inner_comm b z,real_inner_comm x y,
    real_inner_comm x z,real_inner_comm y z,real_inner_comm b a,real_inner_self_eq_norm_sq]
  all_goals ring

theorem doubleFive_coupled_constraints {d : ℕ} (same : Bool) (a b x y z : Mom d)
    (β₁ β₂ τ : ℝ) (hτ : 0 ≤ τ)
    (h₁ : |doubleFiveEnergyOne same (doubleFiveLabels same a b x y z)-β₁| ≤ τ)
    (h₂ : |doubleFiveEnergyTwo same (doubleFiveLabels same a b x y z)-β₂| ≤ τ) :
    |inner ℝ x y-(‖a‖^2-β₁)/2| ≤ τ ∧
      |inner ℝ (if same then x+y-b-z else x-b) z-(‖a+b‖^2-β₁-β₂)/2| ≤ τ := by
  have hs : |(doubleFiveEnergyOne same (doubleFiveLabels same a b x y z)+
      doubleFiveEnergyTwo same (doubleFiveLabels same a b x y z))-(β₁+β₂)| ≤ 2*τ := by
    calc
      _ = |(doubleFiveEnergyOne same (doubleFiveLabels same a b x y z)-β₁)+
          (doubleFiveEnergyTwo same (doubleFiveLabels same a b x y z)-β₂)| := by congr 1; ring
      _ ≤ |doubleFiveEnergyOne same (doubleFiveLabels same a b x y z)-β₁|+
          |doubleFiveEnergyTwo same (doubleFiveLabels same a b x y z)-β₂| := abs_add_le _ _
      _ ≤ τ+τ := add_le_add h₁ h₂
      _ = 2*τ := by ring
  rw [doubleFive_first_energy] at h₁
  rw [doubleFive_combined_energy] at hs
  obtain ⟨h₁l,h₁u⟩ := abs_le.mp h₁
  obtain ⟨hsl,hsu⟩ := abs_le.mp hs
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

end WaveTurbulence.MoleProp
