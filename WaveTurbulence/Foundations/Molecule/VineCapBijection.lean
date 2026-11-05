/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideToCap
public import WaveTurbulence.Foundations.Molecule.VineSideLabels
import Mathlib.Tactic

/-! # Explicit finite label equivalence between a side and a positive cap -/

public section
namespace WaveTurbulence.Vine
open Finset

/-- The three triangle atoms and the contiguous two-rail cap allocation. -/
@[expose] def capLabels (N r : ℕ) : Finset ℕ :=
  {4,5,6} ∪ (range (2*r)).image (N+·)

/-- Cap labels are the triangle or the allocated fresh interval. -/
theorem mem_capLabels_iff (N r a : ℕ) : a ∈ capLabels N r ↔
    a=4 ∨ a=5 ∨ a=6 ∨ (N ≤ a ∧ a<N+2*r) := by
  have hrange : a ∈ (range (2*r)).image (N+·) ↔ N ≤ a ∧ a<N+2*r := by
    constructor
    · rintro ha
      obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
      have := mem_range.mp hi
      constructor <;> omega
    · rintro ⟨hlo,hhi⟩
      exact mem_image.mpr ⟨a-N,mem_range.mpr (by omega),by omega⟩
  simp only [capLabels,mem_union,mem_insert,mem_singleton,hrange,or_assoc]

/-- The explicit cap inverse recovers every available side label. -/
theorem capToSide_sideToCap (N k a : ℕ) (hN : 9 ≤ N) (ha : a ∈ sideLabels N k) :
    capToSide N k (sideToCap N k a)=a := by
  obtain ⟨h4,h5,h6,h7,h8⟩ := sideToCap_core N k hN
  rw [mem_sideLabels_iff] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | ⟨hlo,hhi⟩
  · rw [h4]
    unfold capToSide
    split_ifs <;> omega
  · rw [h5]
    unfold capToSide
    split_ifs <;> omega
  · rw [h6]
    unfold capToSide
    split_ifs <;> omega
  · rw [h7]
    simp only [capToSide,ite_true]
  · rw [h8]
    have he : N+(k+1)+k ≠ N+k := by omega
    simp only [capToSide,he,ite_false,ite_true]
  · have h7a : a ≠ 7 := by omega
    have h8a : a ≠ 8 := by omega
    simp only [sideToCap,h7a,h8a,ite_false]
    by_cases hu : a<N+k
    · have hf : ¬(N+k ≤ a ∧ a<N+2*k) := by omega
      rw [ite_eq_right hf]
      unfold capToSide
      split_ifs <;> omega
    · have ht : N+k ≤ a ∧ a<N+2*k := by omega
      rw [ite_eq_left ht]
      unfold capToSide
      split_ifs <;> omega

/-- Every mapped side atom is an available positive-cap atom. -/
theorem sideToCap_mem (N k a : ℕ) (hN : 9 ≤ N) (ha : a ∈ sideLabels N k) :
    sideToCap N k a ∈ capLabels N (k+1) := by
  obtain ⟨h4,h5,h6,h7,h8⟩ := sideToCap_core N k hN
  rw [mem_sideLabels_iff] at ha
  rw [mem_capLabels_iff]
  rcases ha with rfl | rfl | rfl | rfl | rfl | ⟨hlo,hhi⟩
  · rw [h4]; omega
  · rw [h5]; omega
  · rw [h6]; omega
  · rw [h7]; omega
  · rw [h8]; omega
  · unfold sideToCap
    split_ifs <;> omega

/-- A cap has three triangle atoms and two atoms per full rung. -/
theorem capLabels_card (N r : ℕ) (hN : 9 ≤ N) : (capLabels N r).card=3+2*r := by
  have hd : Disjoint ({4,5,6} : Finset ℕ) ((range (2*r)).image (N+·)) := by
    apply disjoint_left.mpr
    intro a ha hb
    have ha9 : a<9 := by
      simp only [mem_insert,mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> omega
    obtain ⟨i,_hi,he⟩ := mem_image.mp hb
    omega
  rw [capLabels,card_union_of_disjoint hd,
    card_image_of_injective _ (fun _ _ he => Nat.add_left_cancel he),card_range]
  have hc : ({4,5,6} : Finset ℕ).card=3 := by decide
  rw [hc]

/-- The explicit map exhausts every atom of the positive cap exactly once. -/
theorem sideToCap_image (N k : ℕ) (hN : 9 ≤ N) :
    (sideLabels N k).image (sideToCap N k)=capLabels N (k+1) := by
  have hinj : Set.InjOn (sideToCap N k) (sideLabels N k) := by
    intro a ha b hb he
    have hh := congrArg (capToSide N k) he
    rwa [capToSide_sideToCap N k a hN ha,capToSide_sideToCap N k b hN hb] at hh
  apply eq_of_subset_of_card_le
  · intro a ha
    obtain ⟨b,hb,rfl⟩ := mem_image.mp ha
    exact sideToCap_mem N k b hN hb
  · rw [card_image_of_injOn hinj,sideLabels_card N k hN,capLabels_card N (k+1) hN]
    omega

/-- The map followed by its explicit inverse recovers every cap label. -/
theorem sideToCap_capToSide (N k a : ℕ) (hN : 9 ≤ N) (ha : a ∈ capLabels N (k+1)) :
    sideToCap N k (capToSide N k a)=a := by
  rw [← sideToCap_image N k hN] at ha
  obtain ⟨b,hb,rfl⟩ := mem_image.mp ha
  rw [capToSide_sideToCap N k b hN hb]

/-- The inverse maps the cap label set exactly onto the old side label set. -/
theorem capToSide_image (N k : ℕ) (hN : 9 ≤ N) :
    (capLabels N (k+1)).image (capToSide N k)=sideLabels N k := by
  rw [← sideToCap_image N k hN,Finset.image_image]
  ext a
  constructor
  · intro ha
    obtain ⟨b,hb,he⟩ := mem_image.mp ha
    rw [Function.comp_apply,capToSide_sideToCap N k b hN hb] at he
    exact he ▸ hb
  · intro ha
    exact mem_image.mpr ⟨a,ha,capToSide_sideToCap N k a hN ha⟩

end WaveTurbulence.Vine
