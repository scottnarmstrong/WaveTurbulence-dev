/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountFibers
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountBaseLocalized
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountBase
import Mathlib.Tactic

/-! # Actual canonical K4 shell blocks

Both the base-projection estimate and every remaining-label fiber estimate
are proved from the literal source membership. Their finite composition
contains no input counting inequality or cancellation premise.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

/-- The literal elementary majorant for the radius-localized base projection. -/
noncomputable def k4BaseLocalProfile (d : ℕ) (L τ R : ℝ) : ℝ :=
  (d : ℝ)*((2*(L*R)+1)^(d-1)*(2*L+1)^(d-1)*
    (τ*L^2*(3+2*Real.log (⌈2*(L*R)+1⌉₊ : ℝ))+(2*(L*R)+1)))

/-- An actual small-sphere dyadic strip-coefficient block is bounded by
the product of its proved localized base and proved physical fiber profiles. -/
theorem k4_small_sphere_block_le {d : ℕ} (hd : 2 ≤ d)
    (S : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)))
    {L R M τ : ℝ} (hL : 0 < L) (hR : 0 < R) (hM : 0 ≤ M) (hτ : 0 ≤ τ)
    (A : Fin 6 → Mom d) (a b c : Fin d → ℤ) (β : Fin 3 → ℝ)
    (hS : ∀ p ∈ S, p ∈ k4CanonicalSet L A a b c β τ)
    (hneq : ∀ p ∈ S, p.2.1 ≠ a)
    (hr : ∀ p ∈ S, R/2 ≤ ‖latticePoint L c+latticePoint L p.2.1‖ ∧
      ‖latticePoint L c+latticePoint L p.2.1‖ ≤ R)
    (hsmall : ∀ p ∈ S, ‖latticePoint L (k4SphereLabel b p.1 p.2.2)‖ ≤ M) :
    (S.card : ℝ) ≤ k4BaseLocalProfile d L τ R*k4SmallFiberProfile d L τ (R/2) M := by
  classical
  let proj := fun p : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) => (p.1,p.2.1)
  let B := S.image proj
  have hB : (B.card : ℝ) ≤ k4BaseLocalProfile d L τ R := by
    apply k4_base_localized_pair_le B hL hR.le hτ a c (A 1) (β 0)
    intro q hq
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
    have hh := k4CanonicalSet_first (hS p hp)
    refine ⟨hh.1,?_,hneq p hp,hh.2.2.2⟩
    rw [WeylSums.latticePoint_add_eq,add_comm]
    exact (hr p hp).2
  have hF : 0 ≤ k4SmallFiberProfile d L τ (R/2) M := by
    unfold k4SmallFiberProfile
    positivity
  have hfib : ∀ q ∈ B, ((S.filter (fun p => proj p=q)).card : ℝ) ≤ k4SmallFiberProfile d L τ (R/2) M := by
    intro q hq
    obtain ⟨p0,hp0,hp0q⟩ := mem_image.mp hq
    have hy0 : p0.2.1=q.2 := congrArg (fun t : (Fin d → ℤ) × (Fin d → ℤ) => t.2) hp0q
    have hRlower : R/2 ≤ ‖latticePoint L c+latticePoint L q.2‖ := by rw [← hy0]; exact (hr p0 hp0).1
    let T := S.filter (fun p => proj p=q)
    have htbase : ∀ p ∈ T, p.1=q.1 ∧ p.2.1=q.2 := by
      intro p hp
      have he := (mem_filter.mp hp).2
      exact ⟨congrArg (fun t : (Fin d → ℤ) × (Fin d → ℤ) => t.1) he,
        congrArg (fun t : (Fin d → ℤ) × (Fin d → ℤ) => t.2) he⟩
    apply k4_small_sphere_fiber_le hd T hL (div_pos hR (by norm_num)) hM hτ A a b c q.1 q.2 β
      (fun p hp => hS p (mem_filter.mp hp).1) htbase hRlower
    intro p hp
    have hh := hsmall p (mem_filter.mp hp).1
    rw [(htbase p hp).1] at hh
    exact hh
  have hh := Counting.card_le_image_card_mul_of_fiber_le S proj hfib
  exact hh.trans (mul_le_mul_of_nonneg_right hB hF)

/-- Full base-triple count composed with the actual small-sphere fibers.
The outside constant precedes every spatial center and finite source set. -/
theorem k4_full_base_small_sphere_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L ≥ L₀, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
      ∀ (A : Fin 6 → Mom d) (a b c : Fin d → ℤ) (β : Fin 3 → ℝ)
      (S : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))) (R M : ℝ),
      0 < R → 0 ≤ M →
      (∀ p ∈ S, p ∈ k4CanonicalSet L A a b c β (δ⁻¹*L^(-2*γ))) →
      (∀ p ∈ S, R ≤ ‖latticePoint L c+latticePoint L p.2.1‖) →
      (∀ p ∈ S, ‖latticePoint L (k4SphereLabel b p.1 p.2.2)‖ ≤ M) →
      (S.card : ℝ) ≤ C*δ⁻¹*L^(2*((d : ℝ)-γ))*
        k4SmallFiberProfile d L (δ⁻¹*L^(-2*γ)) R M := by
  obtain ⟨C,L₀,hC,hcount⟩ := k4_base_triple_bound d hd γ hγ
  refine ⟨C,max L₀ 1,hC,?_⟩
  intro L hL δ hδ A a b c β S R M hR hM hS hr hsmall
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right L₀ 1).trans hL)
  have hτ : 0 ≤ δ⁻¹*L^(-2*γ) := mul_nonneg (inv_nonneg.mpr hδ.1.le) (Real.rpow_nonneg hLp.le _)
  let proj := fun p : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) => (p.1,p.2.1)
  let B := S.image proj
  have hB : (B.card : ℝ) ≤ C*δ⁻¹*L^(2*((d : ℝ)-γ)) := by
    apply hcount L ((le_max_left L₀ 1).trans hL) δ hδ a (A 0) (A 1) (A 3) (β 0) B
    intro q hq
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
    exact k4CanonicalSet_first (hS p hp)
  have hF : 0 ≤ k4SmallFiberProfile d L (δ⁻¹*L^(-2*γ)) R M := by
    unfold k4SmallFiberProfile
    positivity
  have hfib : ∀ q ∈ B, ((S.filter (fun p => proj p=q)).card : ℝ) ≤
      k4SmallFiberProfile d L (δ⁻¹*L^(-2*γ)) R M := by
    intro q hq
    obtain ⟨p0,hp0,hp0q⟩ := mem_image.mp hq
    have hy0 : p0.2.1=q.2 := congrArg (fun t : (Fin d → ℤ) × (Fin d → ℤ) => t.2) hp0q
    have hRlower : R ≤ ‖latticePoint L c+latticePoint L q.2‖ := by rw [← hy0]; exact hr p0 hp0
    let T := S.filter (fun p => proj p=q)
    have htbase : ∀ p ∈ T, p.1=q.1 ∧ p.2.1=q.2 := by
      intro p hp
      have he := (mem_filter.mp hp).2
      exact ⟨congrArg (fun t : (Fin d → ℤ) × (Fin d → ℤ) => t.1) he,
        congrArg (fun t : (Fin d → ℤ) × (Fin d → ℤ) => t.2) he⟩
    apply k4_small_sphere_fiber_le (by omega : 2 ≤ d) T hLp hR hM hτ A a b c q.1 q.2 β
      (fun p hp => hS p (mem_filter.mp hp).1) htbase hRlower
    intro p hp
    have hh := hsmall p (mem_filter.mp hp).1
    rw [(htbase p hp).1] at hh
    exact hh
  have hh := Counting.card_le_image_card_mul_of_fiber_le S proj hfib
  exact hh.trans (mul_le_mul_of_nonneg_right hB hF)

/-- Full base-triple count composed with actual large-sphere annulus
fibers. All energy and spatial centers are quantified after the constant. -/
theorem k4_full_base_large_sphere_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L ≥ L₀, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
      ∀ (A : Fin 6 → Mom d) (a b c : Fin d → ℤ) (β : Fin 3 → ℝ)
      (S : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))) (M : ℝ),
      0 < M → 1 ≤ L^2*(2*(δ⁻¹*L^(-2*γ))) →
      4*(L^2*(2*(δ⁻¹*L^(-2*γ)))) ≤ ((L*M)/(d : ℝ))^2 →
      (∀ p ∈ S, p ∈ k4CanonicalSet L A a b c β (δ⁻¹*L^(-2*γ))) →
      (∀ p ∈ S, M ≤ ‖latticePoint L (k4SphereLabel b p.1 p.2.2)‖) →
      (S.card : ℝ) ≤ C*δ⁻¹*L^(2*((d : ℝ)-γ))*
        k4LargeFiberProfile d L (δ⁻¹*L^(-2*γ)) M := by
  obtain ⟨C,L₀,hC,hcount⟩ := k4_base_triple_bound d hd γ hγ
  refine ⟨C,max L₀ 1,hC,?_⟩
  intro L hL δ hδ A a b c β S M hM hW hMW hS hlarge
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right L₀ 1).trans hL)
  have hW0 : 0 ≤ L^2*(2*(δ⁻¹*L^(-2*γ))) := zero_le_one.trans hW
  let proj := fun p : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) => (p.1,p.2.1)
  let B := S.image proj
  have hB : (B.card : ℝ) ≤ C*δ⁻¹*L^(2*((d : ℝ)-γ)) := by
    apply hcount L ((le_max_left L₀ 1).trans hL) δ hδ a (A 0) (A 1) (A 3) (β 0) B
    intro q hq
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
    exact k4CanonicalSet_first (hS p hp)
  have hF : 0 ≤ k4LargeFiberProfile d L (δ⁻¹*L^(-2*γ)) M := by
    unfold k4LargeFiberProfile
    positivity
  have hfib : ∀ q ∈ B, ((S.filter (fun p => proj p=q)).card : ℝ) ≤
      k4LargeFiberProfile d L (δ⁻¹*L^(-2*γ)) M := by
    intro q _hq
    let T := S.filter (fun p => proj p=q)
    have htbase : ∀ p ∈ T, p.1=q.1 ∧ p.2.1=q.2 := by
      intro p hp
      have he := (mem_filter.mp hp).2
      exact ⟨congrArg (fun t : (Fin d → ℤ) × (Fin d → ℤ) => t.1) he,
        congrArg (fun t : (Fin d → ℤ) × (Fin d → ℤ) => t.2) he⟩
    apply k4_large_sphere_fiber_le (by omega : 2 ≤ d) T hLp hM hW hMW A a b c q.1 q.2 β
      (fun p hp => hS p (mem_filter.mp hp).1) htbase
    intro p hp
    have hh := hlarge p (mem_filter.mp hp).1
    rw [(htbase p hp).1] at hh
    exact hh
  have hh := Counting.card_le_image_card_mul_of_fiber_le S proj hfib
  exact hh.trans (mul_le_mul_of_nonneg_right hB hF)

end WaveTurbulence.MoleProp
