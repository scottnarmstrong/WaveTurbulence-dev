/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBThreeSignCases
public import WaveTurbulence.Foundations.FinalCount.AppBStarCoordinates
import Mathlib.Tactic

/-! # Finite ordering of two overlapping degree-three supports -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole

def appbOverlapRaw (swap : Bool) (second : Bool) : Fin 3 → Fin 5 :=
  if swap = second then ![0,1,2] else ![0,3,4]

/-- Only finite coordinate and orientation data. Swapping the two source
atoms is necessary when just the second shared label has the middle sign. -/
structure AppbOverlapOrder (σ τ : Fin 3 → ℤˣ) where
  swap : Bool
  profile : Fin 3
  index : Fin 5 ↪ Fin 5
  first : Equiv.Perm (Fin 3)
  second : Equiv.Perm (Fin 3)
  first_indices : ∀ j,appbOverlapRaw swap false (first j) = index (![0,1,2] j)
  second_indices : ∀ j,appbOverlapRaw swap true (second j) = index
    (![ (appbStarSecond profile (fun i : Fin 5 => i)).1,
      (appbStarSecond profile (fun i : Fin 5 => i)).2.1,
      (appbStarSecond profile (fun i : Fin 5 => i)).2.2] j)
  first_same : (if swap then τ else σ) (first 0) = (if swap then τ else σ) (first 2)
  first_opposite : (if swap then τ else σ) (first 0) ≠ (if swap then τ else σ) (first 1)
  second_same : (if swap then σ else τ) (second 0) = (if swap then σ else τ) (second 2)
  second_opposite : (if swap then σ else τ) (second 0) ≠ (if swap then σ else τ) (second 1)

private noncomputable def perm3 (f : Fin 3 → Fin 3) (hf : Function.Bijective f) : Equiv.Perm (Fin 3) := Equiv.ofBijective f hf

/-- Source degree caps imply one of the three canonical coupled profiles. -/
theorem appb_overlap_order_exists (σ τ : Fin 3 → ℤˣ)
    (hσp : ¬∀ i,σ i = 1) (hσm : ¬∀ i,σ i = -1)
    (hτp : ¬∀ i,τ i = 1) (hτm : ¬∀ i,τ i = -1) :
    Nonempty (AppbOverlapOrder σ τ) := by
  rcases appb_three_sign_cases σ hσp hσm with ⟨hs,ho⟩ | ⟨hs,ho⟩ | ⟨hs,ho⟩
  all_goals rcases appb_three_sign_cases τ hτp hτm with ⟨ht,hp⟩ | ⟨ht,hp⟩ | ⟨ht,hp⟩
  · refine ⟨{
        swap := false
        profile := 2,
        index := ⟨![1,0,2,3,4],by decide⟩,
        first := perm3 ![1,0,2] (by decide),
        second := perm3 ![1,0,2] (by decide),
        first_indices := by intro j; fin_cases j <;> rfl,
        second_indices := by intro j; fin_cases j <;> rfl,
        first_same := ?_, first_opposite := ?_, second_same := ?_, second_opposite := ?_ }⟩
    all_goals dsimp only [perm3,Equiv.ofBijective_apply]
    all_goals simp_all
  · refine ⟨{
        swap := false
        profile := 1,
        index := ⟨![1,0,2,4,3],by decide⟩,
        first := perm3 ![1,0,2] (by decide),
        second := perm3 ![0,2,1] (by decide),
        first_indices := by intro j; fin_cases j <;> rfl,
        second_indices := by intro j; fin_cases j <;> rfl,
        first_same := ?_, first_opposite := ?_, second_same := ?_, second_opposite := ?_ }⟩
    all_goals dsimp only [perm3,Equiv.ofBijective_apply]
    all_goals simp_all
  · refine ⟨{
        swap := false
        profile := 1,
        index := ⟨![1,0,2,3,4],by decide⟩,
        first := perm3 ![1,0,2] (by decide),
        second := perm3 ![0,1,2] (by decide),
        first_indices := by intro j; fin_cases j <;> rfl,
        second_indices := by intro j; fin_cases j <;> rfl,
        first_same := ?_, first_opposite := ?_, second_same := ?_, second_opposite := ?_ }⟩
    all_goals dsimp only [perm3,Equiv.ofBijective_apply]
    all_goals simp_all
  · refine ⟨{
        swap := true
        profile := 1,
        index := ⟨![3,0,4,2,1],by decide⟩,
        first := perm3 ![1,0,2] (by decide),
        second := perm3 ![0,2,1] (by decide),
        first_indices := by intro j; fin_cases j <;> rfl,
        second_indices := by intro j; fin_cases j <;> rfl,
        first_same := ?_, first_opposite := ?_, second_same := ?_, second_opposite := ?_ }⟩
    all_goals dsimp only [perm3,Equiv.ofBijective_apply]
    all_goals simp_all
  · refine ⟨{
        swap := false
        profile := 0,
        index := ⟨![1,2,0,4,3],by decide⟩,
        first := perm3 ![1,2,0] (by decide),
        second := perm3 ![0,2,1] (by decide),
        first_indices := by intro j; fin_cases j <;> rfl,
        second_indices := by intro j; fin_cases j <;> rfl,
        first_same := ?_, first_opposite := ?_, second_same := ?_, second_opposite := ?_ }⟩
    all_goals dsimp only [perm3,Equiv.ofBijective_apply]
    all_goals simp_all
  · refine ⟨{
        swap := false
        profile := 0,
        index := ⟨![1,2,0,3,4],by decide⟩,
        first := perm3 ![1,2,0] (by decide),
        second := perm3 ![0,1,2] (by decide),
        first_indices := by intro j; fin_cases j <;> rfl,
        second_indices := by intro j; fin_cases j <;> rfl,
        first_same := ?_, first_opposite := ?_, second_same := ?_, second_opposite := ?_ }⟩
    all_goals dsimp only [perm3,Equiv.ofBijective_apply]
    all_goals simp_all
  · refine ⟨{
        swap := true
        profile := 1,
        index := ⟨![3,0,4,1,2],by decide⟩,
        first := perm3 ![1,0,2] (by decide),
        second := perm3 ![0,1,2] (by decide),
        first_indices := by intro j; fin_cases j <;> rfl,
        second_indices := by intro j; fin_cases j <;> rfl,
        first_same := ?_, first_opposite := ?_, second_same := ?_, second_opposite := ?_ }⟩
    all_goals dsimp only [perm3,Equiv.ofBijective_apply]
    all_goals simp_all
  · refine ⟨{
        swap := false
        profile := 0,
        index := ⟨![2,1,0,4,3],by decide⟩,
        first := perm3 ![2,1,0] (by decide),
        second := perm3 ![0,2,1] (by decide),
        first_indices := by intro j; fin_cases j <;> rfl,
        second_indices := by intro j; fin_cases j <;> rfl,
        first_same := ?_, first_opposite := ?_, second_same := ?_, second_opposite := ?_ }⟩
    all_goals dsimp only [perm3,Equiv.ofBijective_apply]
    all_goals simp_all
  · refine ⟨{
        swap := false
        profile := 0,
        index := ⟨![2,1,0,3,4],by decide⟩,
        first := perm3 ![2,1,0] (by decide),
        second := perm3 ![0,1,2] (by decide),
        first_indices := by intro j; fin_cases j <;> rfl,
        second_indices := by intro j; fin_cases j <;> rfl,
        first_same := ?_, first_opposite := ?_, second_same := ?_, second_opposite := ?_ }⟩
    all_goals dsimp only [perm3,Equiv.ofBijective_apply]
    all_goals simp_all

end WaveTurbulence.Mole
