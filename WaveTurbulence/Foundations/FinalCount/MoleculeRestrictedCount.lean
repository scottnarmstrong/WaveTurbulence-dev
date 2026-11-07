/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBasic
public import WaveTurbulence.Foundations.Counting.LatticeBox
import Mathlib.Tactic

/-!
# Uniform finiteness of restricted molecule decorations

TARGET `defdecmol` L1323 and `defcounta2` L2129: a coordinate box gives
an explicit bound independent of all restriction centers. Consequently
the supremum defining E is finite, not merely each of its terms.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Mole
open Finset Set
open scoped ENNReal
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

private theorem coordinate_choices_card_le {L : ℝ} (hL : 0 < L) (a : ℝ) :
    ((Counting.integerInterval (a-L) (a+L)).card : ℕ∞) ≤ (⌈2*L+1⌉₊ : ℕ∞) := by
  have hreal := (Counting.card_integerInterval_le a hL.le).trans (Nat.le_ceil (2*L+1))
  have hnat : (Counting.integerInterval (a-L) (a+L)).card ≤ ⌈2*L+1⌉₊ := by exact_mod_cast hreal
  exact_mod_cast hnat

/-- Explicit, center-independent bound for all restricted dart labels. -/
theorem restricted_encard_le {d : ℕ} {L : ℝ} (hL : 0 < L) (gamma delta : ℝ)
    (w : Mom d) (beta : V → ℝ) (k0 : D → Mom d) :
    {kappa : D → (Fin d → ℤ) | M.IsRestricted L gamma delta w beta k0 kappa}.encard ≤
      (⌈2*L+1⌉₊ : ℕ∞)^(d*Fintype.card D) := by
  let C (x : D) (j : Fin d) : Finset ℤ := Counting.integerInterval
    (L*((k0 x) j-w j)-L) (L*((k0 x) j-w j)+L)
  let S (x : D) : Set (Fin d → ℤ) := Set.pi Set.univ (fun j => (C x j : Set ℤ))
  have hsub : {kappa : D → (Fin d → ℤ) | M.IsRestricted L gamma delta w beta k0 kappa} ⊆
      Set.pi Set.univ S := by
    intro kappa hk x _hx j _hj
    apply (Counting.mem_integerInterval _ _ _).mpr
    have he := (PiLp.norm_apply_le (p := (2:ENNReal))
      (Molecule.kvec L w kappa x-k0 x) j).trans (hk.2 x)
    have hcoord : |w j+(kappa x j:ℝ)/L-(k0 x) j| ≤ 1 := by
      simpa only [Molecule.kvec,latticePoint,PiLp.sub_apply,PiLp.add_apply,Real.norm_eq_abs] using he
    have hlo : (k0 x) j-w j-1 ≤ (kappa x j:ℝ)/L := by linarith only [(abs_le.mp hcoord).1]
    have hhi : (kappa x j:ℝ)/L ≤ (k0 x) j-w j+1 := by linarith only [(abs_le.mp hcoord).2]
    have hl := (le_div_iff₀ hL).mp hlo
    have hu := (div_le_iff₀ hL).mp hhi
    constructor <;> nlinarith only [hl,hu]
  calc
    _ ≤ (Set.pi Set.univ S).encard := Set.encard_mono hsub
    _ = ∏ x : D, ∏ j : Fin d, (C x j : Set ℤ).encard := by
      simp only [S,Set.encard_pi_eq_prod_encard]
    _ ≤ ∏ _x : D, ∏ _j : Fin d, (⌈2*L+1⌉₊ : ℕ∞) := by
      apply Finset.prod_le_prod
      intro x _hx
      apply Finset.prod_le_prod
      intro j _hj
      rw [Set.encard_coe_eq_coe_finsetCard]
      exact coordinate_choices_card_le hL _
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← pow_mul]

/-- Every actual restricted decoration set is finite for positive scale. -/
theorem finite_restricted {d : ℕ} {L : ℝ} (hL : 0 < L) (gamma delta : ℝ)
    (w : Mom d) (beta : V → ℝ) (k0 : D → Mom d) :
    {kappa : D → (Fin d → ℤ) | M.IsRestricted L gamma delta w beta k0 kappa}.Finite := by
  apply Set.finite_of_encard_le_coe (k := ⌈2*L+1⌉₊^(d*Fintype.card D))
  simpa only [Nat.cast_pow] using restricted_encard_le M hL gamma delta w beta k0

/-- The bound is uniform over every parameter in the exact draft supremum E. -/
theorem countE_le {d : ℕ} {L : ℝ} (hL : 0 < L) (gamma delta : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) :
    M.countE L gamma delta w Adm ≤ (⌈2*L+1⌉₊ : ℕ∞)^(d*Fintype.card D) := by
  unfold Molecule.countE
  refine iSup_le fun c => iSup_le fun _hc => iSup_le fun beta => iSup_le fun k0 => iSup_le fun _hk0 => ?_
  exact (Set.encard_mono (fun _kappa h => h.2.1)).trans (restricted_encard_le M hL gamma delta w beta k0)

/-- Positive lattice scale rules out an infinite count, including after
maximizing over restriction centers and conservation parameters. -/
theorem countE_ne_top {d : ℕ} {L : ℝ} (hL : 0 < L) (gamma delta : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) : M.countE L gamma delta w Adm ≠ ⊤ := by
  exact ne_top_of_le_ne_top (by simp) (countE_le M hL gamma delta w Adm)

end WaveTurbulence.Mole
