/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.OneSharedTripleCount
import Mathlib.Tactic

/-! # The unbalanced virtual four-star of DH23 Proposition 10.3

The first star is (++−); the second is (−−+−), sharing its first two
labels. Such a virtual star must not be assigned the original graph's
balanced-four-star premise. Its exact count is coupled-triple selector1.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
open CountLemmas

def unbalancedLabels {E : Type*} [AddCommGroup E] (a b x y z : E) : Fin 5 → E :=
  ![x+a,y+a,x+y+a,x+y+a+z,z-(a+b)]

def UnbalancedMomentum {E : Type*} [AddCommGroup E] (a b : E) (k : Fin 5 → E) : Prop :=
  k 0+k 1-k 2=a ∧ -k 0-k 1+k 3-k 4=b

def unbalancedCoordinates {E : Type*} [AddCommGroup E] (a b : E) (k : Fin 5 → E) : E × E × E :=
  (k 0-a,k 1-a,k 4+(a+b))

theorem unbalancedLabels_reconstruct {E : Type*} [AddCommGroup E]
    (a b : E) (k : Fin 5 → E) (hk : UnbalancedMomentum a b k) :
    k=unbalancedLabels a b (unbalancedCoordinates a b k).1
      (unbalancedCoordinates a b k).2.1 (unbalancedCoordinates a b k).2.2 := by
  have h2 : k 2=k 0+k 1-a := by rw [← hk.1]; abel
  have h3 : k 3=k 0+k 1+k 4+b := by rw [← hk.2]; abel
  funext i
  fin_cases i <;> simp [unbalancedLabels,unbalancedCoordinates,h2,h3]
  all_goals abel

noncomputable def unbalancedEnergyOne {d : ℕ} (k : Fin 5 → Mom d) : ℝ :=
  ‖k 0‖^2+‖k 1‖^2-‖k 2‖^2
noncomputable def unbalancedEnergyTwo {d : ℕ} (k : Fin 5 → Mom d) : ℝ :=
  -‖k 0‖^2-‖k 1‖^2+‖k 3‖^2-‖k 4‖^2

theorem unbalanced_first_energy {d : ℕ} (a b x y z : Mom d) :
    unbalancedEnergyOne (unbalancedLabels a b x y z)=‖a‖^2-2*inner ℝ x y := by
  simp [unbalancedEnergyOne,unbalancedLabels,norm_add_sq_real,inner_add_left]
  simp only [real_inner_comm y x,real_inner_comm a x,real_inner_comm a y]
  ring

theorem unbalanced_combined_energy {d : ℕ} (a b x y z : Mom d) :
    unbalancedEnergyOne (unbalancedLabels a b x y z)+unbalancedEnergyTwo (unbalancedLabels a b x y z)=
      -‖a+b‖^2+2*inner ℝ (x+y+a+(a+b)) z := by
  simp [unbalancedEnergyOne,unbalancedEnergyTwo,unbalancedLabels,norm_add_sq_real,norm_sub_sq_real,
    inner_add_left,inner_add_right,inner_sub_left,inner_sub_right]
  simp only [real_inner_comm a x,real_inner_comm a y,real_inner_comm a z,real_inner_comm b x,
    real_inner_comm b y,real_inner_comm b z,real_inner_comm x y,real_inner_comm x z,
    real_inner_comm y z,real_inner_comm b a,real_inner_self_eq_norm_sq]
  ring

def UnbalancedSource {d : ℕ} (L : ℝ) (a b : Fin d → ℤ) (β₁ β₂ τ : ℝ)
    (centers : Fin 5 → Mom d) (k : Fin 5 → (Fin d → ℤ)) : Prop :=
  UnbalancedMomentum a b k ∧ (∀ i, NearLattice L (centers i) (k i)) ∧
    |unbalancedEnergyOne (fun i => latticePoint L (k i))-β₁| ≤ τ ∧
    |unbalancedEnergyTwo (fun i => latticePoint L (k i))-β₂| ≤ τ

theorem latticePoint_unbalancedLabels {d : ℕ} (L : ℝ) (a b x y z : Fin d → ℤ) :
    (fun i => latticePoint L (unbalancedLabels a b x y z i)) =
      unbalancedLabels (latticePoint L a) (latticePoint L b) (latticePoint L x) (latticePoint L y) (latticePoint L z) := by
  funext i
  fin_cases i <;> simp [unbalancedLabels,WeylSums.latticePoint_add_eq,WeylSums.latticePoint_sub_eq]

theorem unbalancedCoordinates_mem_coupledTripleSet {d : ℕ} (L : ℝ) (a b : Fin d → ℤ)
    (β₁ β₂ τ : ℝ) (hτ : 0 ≤ τ) (centers : Fin 5 → Mom d) (k : Fin 5 → (Fin d → ℤ))
    (hk : UnbalancedSource L a b β₁ β₂ τ centers k) :
    unbalancedCoordinates a b k ∈ coupledTripleSet L (centers 0-latticePoint L a)
      (centers 1-latticePoint L a) (centers 4+latticePoint L (a+b))
      (latticePoint L (-(a+(a+b)))) ((‖latticePoint L a‖^2-β₁)/2)
      ((β₁+β₂+‖latticePoint L (a+b)‖^2)/2) τ 1 := by
  obtain ⟨hm,hn,h₁,h₂⟩ := hk
  have hrec := unbalancedLabels_reconstruct a b k hm
  have hphys : (fun i => latticePoint L (k i)) = unbalancedLabels (latticePoint L a) (latticePoint L b)
      (latticePoint L (unbalancedCoordinates a b k).1) (latticePoint L (unbalancedCoordinates a b k).2.1)
      (latticePoint L (unbalancedCoordinates a b k).2.2) := by
    conv_lhs => rw [hrec]
    exact latticePoint_unbalancedLabels L a b _ _ _
  have hsum := add_le_add (abs_le.mp h₁).1 (abs_le.mp h₂).1
  have hsum' := add_le_add (abs_le.mp h₁).2 (abs_le.mp h₂).2
  rw [hphys,unbalanced_first_energy] at h₁
  have hslo : -2*τ ≤ unbalancedEnergyOne (fun i => latticePoint L (k i))+
      unbalancedEnergyTwo (fun i => latticePoint L (k i))-(β₁+β₂) := by linarith only [hsum]
  have hshi : unbalancedEnergyOne (fun i => latticePoint L (k i))+
      unbalancedEnergyTwo (fun i => latticePoint L (k i))-(β₁+β₂) ≤ 2*τ := by linarith only [hsum']
  rw [hphys,unbalanced_combined_energy] at hslo hshi
  have hoff : latticePoint L (-(a+(a+b))) = -(latticePoint L a+(latticePoint L a+latticePoint L b)) := by
    change latticePointHom L (-(a+(a+b))) = _
    simp only [map_neg,map_add,latticePointHom_apply]
  refine ⟨nearLattice_sub_fixed L _ _ a (hn 0),nearLattice_sub_fixed L _ _ a (hn 1),
    nearLattice_add_fixed L _ _ (a+b) (hn 4),?_,?_⟩
  · obtain ⟨hl,hu⟩ := abs_le.mp h₁
    apply abs_le.mpr
    constructor <;> linarith
  · simp only [add_assoc] at hslo hshi
    change |inner ℝ (latticePoint L (unbalancedCoordinates a b k).1+
      latticePoint L (unbalancedCoordinates a b k).2.1-latticePoint L (-(a+(a+b))))
      (latticePoint L (unbalancedCoordinates a b k).2.2)-
      (β₁+β₂+‖latticePoint L (a+b)‖^2)/2| ≤ τ
    rw [hoff,WeylSums.latticePoint_add_eq]
    simp only [sub_neg_eq_add,add_assoc]
    apply abs_le.mpr
    constructor <;> linarith

/-- Conditional local source bound for the unbalanced virtual quad. -/
theorem unbalanced_double_local_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C R : ℝ, 0 < C ∧ ∀ L ≥ R, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (a b : Fin d → ℤ) (β₁ β₂ : ℝ) (centers : Fin 5 → Mom d) (S : Finset (Fin 5 → (Fin d → ℤ))),
      (∀ k ∈ S, UnbalancedSource L a b β₁ β₂ (δ⁻¹*L^(-2*γ)) centers k) →
      (S.card : ℝ) ≤ C*δ⁻¹^2*L^(3*((d : ℝ)-γ)-min γ (1-γ)) := by
  classical
  obtain ⟨C,R,hC,hB⟩ := coupledTriple_bound d hd γ hγ
  refine ⟨C,max R 1,hC,?_⟩
  intro L hL δ hδ a b β₁ β₂ centers S hS
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right R 1).trans hL)
  have hτ : 0 ≤ δ⁻¹*L^(-2*γ) := mul_nonneg (inv_nonneg.mpr hδ.1.le) (Real.rpow_nonneg hLp.le _)
  let α := (‖latticePoint L a‖^2-β₁)/2
  let β := (β₁+β₂+‖latticePoint L (a+b)‖^2)/2
  let T := S.image (unbalancedCoordinates a b)
  have hinj : Set.InjOn (unbalancedCoordinates a b) S := by
    intro k hk k' hk' he
    rw [unbalancedLabels_reconstruct a b k (hS k hk).1,unbalancedLabels_reconstruct a b k' (hS k' hk').1,he]
  have hcard : T.card=S.card := card_image_of_injOn hinj
  obtain ⟨hf,hb⟩ := hB L ((le_max_left R 1).trans hL) δ hδ
    (centers 0-latticePoint L a) (centers 1-latticePoint L a) (centers 4+latticePoint L (a+b))
    (-(a+(a+b))) 1 α β
  have hsub : (T : Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))) ⊆
      coupledTripleSet L (centers 0-latticePoint L a) (centers 1-latticePoint L a)
        (centers 4+latticePoint L (a+b)) (latticePoint L (-(a+(a+b)))) α β (δ⁻¹*L^(-2*γ)) 1 := by
    intro z hz
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hz
    exact unbalancedCoordinates_mem_coupledTripleSet L a b β₁ β₂ _ hτ centers k (hS k hk)
  have hn : T.card ≤ (coupledTripleSet L (centers 0-latticePoint L a) (centers 1-latticePoint L a)
      (centers 4+latticePoint L (a+b)) (latticePoint L (-(a+(a+b)))) α β (δ⁻¹*L^(-2*γ)) 1).ncard := by
    simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub hf
  have hnR : (T.card : ℝ) ≤ (coupledTripleSet L (centers 0-latticePoint L a) (centers 1-latticePoint L a)
      (centers 4+latticePoint L (a+b)) (latticePoint L (-(a+(a+b)))) α β (δ⁻¹*L^(-2*γ)) 1).ncard := by exact_mod_cast hn
  rw [hcard] at hnR
  exact hnR.trans hb

end WaveTurbulence.MoleProp
