/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.AtomTriple
import Mathlib.Tactic

/-! # The full actual base-triple projection of a canonical K4 fiber

This is a direct finite injection into the landed signed three-vector
count. It complements the radius-localized elementary estimate.
-/

@[expose] public section
set_option autoImplicit false
open Finset Set
namespace WaveTurbulence.MoleProp
open CountLemmas

/-- The canonical first-vertex base projection satisfies the full triple
bound uniformly in all conserved and spatial/energy centers. -/
theorem k4_base_triple_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L ≥ L₀, ∀ δ ∈ Ioc (0 : ℝ) 1,
      ∀ a : Fin d → ℤ, ∀ A0 A1 A3 : Mom d, ∀ β : ℝ,
      ∀ S : Finset ((Fin d → ℤ) × (Fin d → ℤ)),
      (∀ p ∈ S, NearLattice L A1 p.1 ∧ NearLattice L A3 p.2 ∧
        NearLattice L A0 (p.1+p.2-a) ∧
        |-‖latticePoint L (p.1+p.2-a)‖^2+‖latticePoint L p.1‖^2+
          ‖latticePoint L p.2‖^2-β| ≤ δ⁻¹*L^(-2*γ)) →
      (S.card : ℝ) ≤ C*δ⁻¹*L^(2*((d : ℝ)-γ)) := by
  obtain ⟨C,L₀,hbound⟩ := atomTriple_bound d hd γ hγ
  refine ⟨|C|+1,max L₀ 1,by positivity,?_⟩
  intro L hL δ hδ a A0 A1 A3 β S hS
  let f := fun p : (Fin d → ℤ) × (Fin d → ℤ) => (p.1,p.1+p.2-a,p.2)
  obtain ⟨hfinite,hb⟩ := hbound L ((le_max_left L₀ 1).trans hL) δ hδ β a A1 A0 A3
  have hmaps : (S.image f : Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))) ⊆
      atomTripleSet L A1 A0 A3 a β (δ⁻¹*L^(-2*γ)) := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
    have hs := hS p hp
    refine ⟨hs.1,hs.2.2.1,hs.2.1,?_,?_⟩
    · funext i
      change p.1 i-(p.1 i+p.2 i-a i)+p.2 i=a i
      omega
    · change |‖latticePoint L p.1‖^2-‖latticePoint L (p.1+p.2-a)‖^2+
        ‖latticePoint L p.2‖^2-β| ≤ _
      convert hs.2.2.2 using 1 <;> congr 1 <;> ring
  have hinj : Set.InjOn f (S : Set ((Fin d → ℤ) × (Fin d → ℤ))) := by
    intro p _hp q _hq he
    have hx : p.1=q.1 := congrArg (fun t : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) => t.1) he
    have hy : p.2=q.2 := congrArg (fun t : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) => t.2.2) he
    exact Prod.ext hx hy
  have hcard := Set.ncard_le_ncard hmaps hfinite
  have hcardR : (S.card : ℝ) ≤ ((atomTripleSet L A1 A0 A3 a β (δ⁻¹*L^(-2*γ))).ncard : ℝ) := by
    rw [Set.ncard_coe_finset,card_image_of_injOn hinj] at hcard
    exact_mod_cast hcard
  have hC : C ≤ |C|+1 := by linarith only [le_abs_self C]
  have hm : C*δ⁻¹*L^(2*((d : ℝ)-γ)) ≤ (|C|+1)*δ⁻¹*L^(2*((d : ℝ)-γ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (inv_nonneg.mpr hδ.1.le))
      (Real.rpow_nonneg (zero_lt_one.trans_le ((le_max_right L₀ 1).trans hL)).le _)
  exact hcardR.trans (hb.trans hm)

end WaveTurbulence.MoleProp
