/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.LatticeSets
import Mathlib.Tactic

/-! # Exceptional fixed coefficient vectors in the canonical K4 count

Zero bilinear or strip coefficients fix one of the three free vectors.
The remaining actual unit-ball lattice labels have an elementary 2d
box bound, already below the desired K4 exponent.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
open CountLemmas

/-- Fixing the middle free vector leaves exactly two actual lattice labels
to count; no nondegeneracy or large-gap premise is necessary. -/
theorem k4_fixed_middle_card_le {d : ℕ}
    (S : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)))
    {L : ℝ} (hL : 0 < L) (ax az : Mom d) (y : Fin d → ℤ)
    (hS : ∀ q ∈ S, NearLattice L ax q.1 ∧ NearLattice L az q.2.2 ∧ q.2.1=y) :
    (S.card : ℝ) ≤ (2*L+1)^(2*d) := by
  classical
  let f := fun q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) => (q.1,q.2.2)
  let Bx := Counting.latticeBox (fun i => L*ax i) L
  let Bz := Counting.latticeBox (fun i => L*az i) L
  have hinj : Set.InjOn f (S : Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))) := by
    intro q hq p hp he
    have he' : (q.1,q.2.2)=(p.1,p.2.2) := he
    have hx := congrArg Prod.fst he'
    have hz := congrArg Prod.snd he' 
    exact Prod.ext hx (Prod.ext ((hS q hq).2.2.trans (hS p hp).2.2.symm) hz)
  have hsub : S.image f ⊆ Bx ×ˢ Bz := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
    exact mem_product.mpr ⟨nearLattice_mem_box hL ax q.1 (hS q hq).1,
      nearLattice_mem_box hL az q.2.2 (hS q hq).2.1⟩
  have hc : (S.card : ℝ) ≤ (Bx.card : ℝ)*(Bz.card : ℝ) := by
    have hh := card_le_card hsub
    rw [card_image_of_injOn hinj,card_product] at hh
    exact_mod_cast hh
  have hx := Counting.card_latticeBox_le (fun i => L*ax i) hL.le
  have hz := Counting.card_latticeBox_le (fun i => L*az i) hL.le
  have hh := mul_le_mul hx hz (Nat.cast_nonneg Bz.card) (by positivity : 0 ≤ (2*L+1)^d)
  have he : (2*L+1)^d*(2*L+1)^d = (2*L+1)^(2*d) := by rw [← pow_add]; congr 1; omega
  exact hc.trans (hh.trans_eq he)

end WaveTurbulence.MoleProp
