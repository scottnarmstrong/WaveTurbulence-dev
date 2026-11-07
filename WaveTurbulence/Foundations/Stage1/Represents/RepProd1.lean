/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RepAnalytic.ProductFubini
import Mathlib.Tactic

/-!
# S2 REPRESENTS: products of superpositions over a finite index type
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Represents
open Finset
open scoped ENNReal

/-- Product of absolutely summable families over a finite index type with dependent mode types. -/
theorem hasSum_prod_fintype {ι : Type} [Fintype ι] {M : ι → Type} (u : ∀ i, M i → ℂ)
    (hs : ∀ i, Summable fun m => ‖u i m‖) :
    Summable (fun m : ∀ i, M i => ‖∏ i, u i (m i)‖) ∧
      HasSum (fun m : ∀ i, M i => ∏ i, u i (m i)) (∏ i, ∑' m, u i m) := by
  classical
  let e := (Fintype.equivFin ι).symm
  let E : (∀ j : Fin (Fintype.card ι), M (e j)) ≃ ∀ i, M i := Equiv.piCongrLeft M e
  have key := RepAnalytic.hasSum_pi_prod_dep (𝕜 := ℂ) (Fintype.card ι) (M := fun j => M (e j))
    (fun j => u (e j)) (fun j => hs (e j))
  have hprod : ∀ m : (∀ j : Fin (Fintype.card ι), M (e j)),
      ∏ j, u (e j) (m j) = ∏ i, u i (E m i) := by
    intro m
    refine Fintype.prod_equiv e _ _ fun j => ?_
    simp only [E, Equiv.piCongrLeft_apply_apply]
  have hprod2 : ∏ j, ∑' x, u (e j) x = ∏ i, ∑' x, u i x := Fintype.prod_equiv e _ _ fun j => rfl
  refine ⟨?_, ?_⟩
  · rw [← E.summable_iff]
    refine key.1.congr fun m => ?_
    simp only [Function.comp, ← hprod]
  · rw [← E.hasSum_iff, ← hprod2]
    refine key.2.congr_fun ?_
    intro m
    simp only [Function.comp, ← hprod]

theorem tsum_ofReal_prod_fintype {ι : Type} [Fintype ι] {M : ι → Type} (w : ∀ i, M i → ℝ)
    (hw : ∀ i m, 0 ≤ w i m) :
    ∑' m : ∀ i, M i, ENNReal.ofReal (∏ i, w i (m i)) = ∏ i, ∑' m, ENNReal.ofReal (w i m) := by
  classical
  let e := (Fintype.equivFin ι).symm
  let E : (∀ j : Fin (Fintype.card ι), M (e j)) ≃ ∀ i, M i := Equiv.piCongrLeft M e
  have key := RepAnalytic.tsum_ofReal_prod (n := Fintype.card ι) (M := fun j => M (e j))
    (fun j => w (e j)) (fun j => hw (e j))
  have hprod : ∀ m : (∀ j : Fin (Fintype.card ι), M (e j)),
      ∏ j, w (e j) (m j) = ∏ i, w i (E m i) := by
    intro m
    refine Fintype.prod_equiv e _ _ fun j => ?_
    simp only [E, Equiv.piCongrLeft_apply_apply]
  have hprod2 : ∏ j, ∑' x, ENNReal.ofReal (w (e j) x) = ∏ i, ∑' x, ENNReal.ofReal (w i x) :=
    Fintype.prod_equiv e _ _ fun j => rfl
  rw [← E.tsum_eq, ← hprod2, ← key]
  exact tsum_congr fun m => by rw [hprod]

end WaveTurbulence.Represents
