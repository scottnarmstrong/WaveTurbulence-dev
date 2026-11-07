/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DoublePairAlgebra
public import WaveTurbulence.Foundations.FinalCount.MoleProp.LatticeHom
import Mathlib.Tactic

/-! # The one-shared-label five-variable systems of DH23 basiccount(4)

Modes distinguish the shared label's majority/minority position. They are
explicit algebraic conditional helpers for the good-step reductions, not
a graph configuration theorem or a Proposition 10.3 endpoint.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

/-- Mode0: shared-majority in both stars. Mode1: shared-minority first,
shared-majority second. Mode2: shared-minority in both normalized stars. -/
def oneSharedLabels {E : Type*} [AddCommGroup E] (mode : Fin 3) (a b x y z : E) : Fin 5 → E :=
  if mode=0 then ![x+a,x+y+a,y+a,x+a+z,z-b]
  else if mode=1 then ![x+y+a,x+a,y+a,z+b,x+y+a+z]
  else ![x+y+a,x+a,y+a,z+b,x+y+a-z]

def OneSharedMomentum {E : Type*} [AddCommGroup E] (mode : Fin 3) (a b : E) (k : Fin 5 → E) : Prop :=
  (if mode=0 then k 0-k 1+k 2=a else k 1+k 2-k 0=a) ∧
    (if mode=0 then -k 0+k 3-k 4=b else if mode=1 then k 0+k 3-k 4=b else -k 0+k 3+k 4=b)

def oneSharedCoordinates {E : Type*} [AddCommGroup E] (mode : Fin 3) (a b : E)
    (k : Fin 5 → E) : E × E × E :=
  (if mode=0 then k 0-a else k 1-a,k 2-a,if mode=0 then k 4+b else k 3-b)

def oneSharedOffset {E : Type*} [AddCommGroup E] (mode : Fin 3) (a b : E) : E :=
  if mode=0 then -(a+b) else b-a

theorem oneSharedLabels_reconstruct {E : Type*} [AddCommGroup E] (mode : Fin 3)
    (a b : E) (k : Fin 5 → E) (hk : OneSharedMomentum mode a b k) :
    k = oneSharedLabels mode a b (oneSharedCoordinates mode a b k).1
      (oneSharedCoordinates mode a b k).2.1 (oneSharedCoordinates mode a b k).2.2 := by
  fin_cases mode
  · have h : k 0-k 1+k 2=a ∧ -k 0+k 3-k 4=b := hk
    have h1 : k 1=k 0+k 2-a := by rw [← h.1]; abel
    have h3 : k 3=k 0+k 4+b := by rw [← h.2]; abel
    funext i
    fin_cases i <;> simp [oneSharedLabels,oneSharedCoordinates,h1,h3]
    all_goals abel
  · have h : k 1+k 2-k 0=a ∧ k 0+k 3-k 4=b := hk
    have h0 : k 0=k 1+k 2-a := by rw [← h.1]; abel
    have h4 : k 4=k 0+k 3-b := by rw [← h.2]; abel
    funext i
    fin_cases i <;> simp [oneSharedLabels,oneSharedCoordinates,h0,h4]
    all_goals abel
  · have h : k 1+k 2-k 0=a ∧ -k 0+k 3+k 4=b := hk
    have h0 : k 0=k 1+k 2-a := by rw [← h.1]; abel
    have h4 : k 4=k 0-k 3+b := by rw [← h.2]; abel
    funext i
    fin_cases i <;> simp [oneSharedLabels,oneSharedCoordinates,h0,h4]
    all_goals abel

noncomputable def oneSharedEnergyOne {d : ℕ} (mode : Fin 3) (k : Fin 5 → Mom d) : ℝ :=
  if mode=0 then ‖k 0‖^2-‖k 1‖^2+‖k 2‖^2 else -‖k 0‖^2+‖k 1‖^2+‖k 2‖^2

noncomputable def oneSharedEnergyTwo {d : ℕ} (mode : Fin 3) (k : Fin 5 → Mom d) : ℝ :=
  if mode=0 then -‖k 0‖^2+‖k 3‖^2-‖k 4‖^2
  else if mode=1 then ‖k 0‖^2+‖k 3‖^2-‖k 4‖^2 else -‖k 0‖^2+‖k 3‖^2+‖k 4‖^2

theorem oneShared_first_energy {d : ℕ} (mode : Fin 3) (a b x y z : Mom d) :
    oneSharedEnergyOne mode (oneSharedLabels mode a b x y z) = ‖a‖^2-2*inner ℝ x y := by
  fin_cases mode <;> simp [oneSharedEnergyOne,oneSharedLabels,norm_add_sq_real,inner_add_left]
  all_goals simp only [real_inner_comm y x,real_inner_comm a x,real_inner_comm a y]
  all_goals ring

theorem oneShared_second_energy {d : ℕ} (mode : Fin 3) (a b x y z : Mom d) :
    oneSharedEnergyTwo mode (oneSharedLabels mode a b x y z) = (if mode=0 then -‖b‖^2 else ‖b‖^2)+
      (if mode=0 then 2 else -2)*inner ℝ
        (![x-oneSharedOffset mode a b,x+y-oneSharedOffset mode a b,
            x+y-oneSharedOffset mode a b-z] mode) z := by
  fin_cases mode <;> simp [oneSharedEnergyTwo,oneSharedLabels,oneSharedOffset,
    norm_add_sq_real,norm_sub_sq_real,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right]
  all_goals simp only [real_inner_comm a x,real_inner_comm a y,real_inner_comm a z,
    real_inner_comm b x,real_inner_comm b y,real_inner_comm b z,real_inner_comm x y,
    real_inner_comm x z,real_inner_comm y z,real_inner_comm b a,real_inner_self_eq_norm_sq]
  all_goals ring

theorem oneShared_coupled_constraints {d : ℕ} (mode : Fin 3) (a b x y z : Mom d)
    (β₁ β₂ τ : ℝ) (hτ : 0 ≤ τ)
    (h₁ : |oneSharedEnergyOne mode (oneSharedLabels mode a b x y z)-β₁| ≤ τ)
    (h₂ : |oneSharedEnergyTwo mode (oneSharedLabels mode a b x y z)-β₂| ≤ τ) :
    |inner ℝ x y-(‖a‖^2-β₁)/2| ≤ τ ∧
      |inner ℝ (![x-oneSharedOffset mode a b,x+y-oneSharedOffset mode a b,
        x+y-oneSharedOffset mode a b-z] mode) z-
        (if mode=0 then (β₂+‖b‖^2)/2 else (‖b‖^2-β₂)/2)| ≤ τ := by
  rw [oneShared_first_energy] at h₁
  rw [oneShared_second_energy] at h₂
  obtain ⟨h₁l,h₁u⟩ := abs_le.mp h₁
  obtain ⟨h₂l,h₂u⟩ := abs_le.mp h₂
  constructor
  · apply abs_le.mpr
    constructor <;> linarith
  · by_cases hm : mode=0 <;> simp only [hm,ite_true,ite_false] at h₂l h₂u ⊢ <;>
      apply abs_le.mpr <;> constructor <;> linarith

end WaveTurbulence.MoleProp
