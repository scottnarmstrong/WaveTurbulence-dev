/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCounting
import Mathlib.Tactic

/-! # Physical decorations under actual dart relabeling with fixed atoms

This is a transport API for the literal flattening of successive deletions.
It introduces no new molecule notion or substitute counting quantity.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset

def relabelLabels {D E K : Type*} (f : D ≃ E) (κ : D → K) : E → K := κ ∘ f.symm

theorem relabelLabels_injective {D E K : Type*} (f : D ≃ E) :
    Function.Injective (relabelLabels (K := K) f) := by
  intro κ κ' he
  funext x
  have hh := congrFun he (f x)
  simpa only [relabelLabels,Function.comp_apply,f.symm_apply_apply] using hh

variable {V D E : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

theorem sum_dartsAt_relabel (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (ha : ∀ x,N.atom (f x) = M.atom x) (a : V)
    {K : Type*} [AddCommMonoid K] (g : E → K) :
    (∑ x ∈ M.dartsAt a,g (f x)) = ∑ y ∈ N.dartsAt a,g y := by
  apply sum_bij (fun x _ => f x)
  · intro x hx
    exact mem_filter.mpr ⟨mem_univ _,(ha x).trans (mem_filter.mp hx).2⟩
  · intro x hx y hy he
    exact f.injective he
  · intro y hy
    obtain ⟨x,rfl⟩ := f.surjective y
    exact ⟨x,mem_filter.mpr ⟨mem_univ _,(ha x).symm.trans (mem_filter.mp hy).2⟩,rfl⟩
  · intro x hx
    rfl

theorem relabel_inverse_mate (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (hm : ∀ x,N.mate (f x) = f (M.mate x)) (y : E) :
    f.symm (N.mate y) = M.mate (f.symm y) := by
  apply f.injective
  rw [f.apply_symm_apply,← hm,f.apply_symm_apply]

theorem momentum_sum_relabel (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (ha : ∀ x,N.atom (f x) = M.atom x) (ho : ∀ x,N.out (f x) = M.out x)
    {d : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (a : V) :
    (∑ y ∈ N.dartsAt a,N.dartSign y • Molecule.kvec L w (relabelLabels f κ) y) =
      ∑ x ∈ M.dartsAt a,M.dartSign x • Molecule.kvec L w κ x := by
  rw [← sum_dartsAt_relabel M N f ha a]
  apply sum_congr rfl
  intro x hx
  simp only [Molecule.dartSign,ho,relabelLabels,Function.comp_apply,Molecule.kvec,f.symm_apply_apply]

theorem gamma_relabel (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (ha : ∀ x,N.atom (f x) = M.atom x) (ho : ∀ x,N.out (f x) = M.out x)
    {d : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (a : V) :
    N.Gamma L w (relabelLabels f κ) a = M.Gamma L w κ a := by
  unfold Molecule.Gamma
  rw [← sum_dartsAt_relabel M N f ha a]
  apply sum_congr rfl
  intro x hx
  simp only [Molecule.dartSign,ho,relabelLabels,Function.comp_apply,Molecule.kvec,f.symm_apply_apply]

theorem isDecoration_relabel (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (hA : M.atoms = N.atoms) (ha : ∀ x,N.atom (f x) = M.atom x)
    (hm : ∀ x,N.mate (f x) = f (M.mate x)) (ho : ∀ x,N.out (f x) = M.out x)
    {d : ℕ} (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) : N.IsDecoration L w c (relabelLabels f κ) := by
  constructor
  · intro y
    change κ (f.symm (N.mate y)) = κ (f.symm y)
    rw [relabel_inverse_mate M N f hm]
    exact hκ.1 _
  · intro a haN
    rw [momentum_sum_relabel M N f ha ho]
    exact hκ.2 a (hA.symm ▸ haN)

theorem isRestricted_relabel (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (hA : M.atoms = N.atoms) (ha : ∀ x,N.atom (f x) = M.atom x) (ho : ∀ x,N.out (f x) = M.out x)
    {d : ℕ} (L γ δ : ℝ) (w : Mom d) (β : V → ℝ) (k0 : D → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsRestricted L γ δ w β k0 κ) :
    N.IsRestricted L γ δ w β (k0 ∘ f.symm) (relabelLabels f κ) := by
  constructor
  · intro a haN
    rw [gamma_relabel M N f ha ho]
    exact hκ.1 a (hA.symm ▸ haN)
  · intro y
    exact hκ.2 (f.symm y)

end WaveTurbulence.Mole.AppbAlgorithm
