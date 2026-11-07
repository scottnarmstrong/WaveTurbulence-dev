/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepCount1
import Mathlib.Tactic

/-!
# S2 REPRESENTS: decorations whose bond momenta lie in unit balls are uniformly few
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine

variable {w d : ℕ} {S : Garden w}

open scoped Classical in
theorem decoration_count (hS : S.IsPlain) (L : ℝ) (hL : 0 < L) (base : Mom d) (roots : Fin w → Fin d → ℤ)
    (c : ReplacementSlot S → Mom d) :
    {κ : GenDecoration S d roots 0 |
        ∀ s, hasBond hS s → ‖base + latticePoint L (κ.1 (slotNode hS s)) - c s‖ ≤ 1}.Finite ∧
      {κ : GenDecoration S d roots 0 |
        ∀ s, hasBond hS s → ‖base + latticePoint L (κ.1 (slotNode hS s)) - c s‖ ≤ 1}.ncard ≤
      ((⌊2 * L⌋₊ + 2) ^ d) ^ Fintype.card (SourcePair S) := by
  choose F hFcard hFmem using fun p : SourcePair S => ball_finset L hL (base - c (Sum.inl p))
  let Bnd : SourcePair S → Finset (Fin d → ℤ) := fun p =>
    if hasBond hS (Sum.inl p) then F p else {kconstInt hS roots (Sum.inl p)}
  let Φ : GenDecoration S d roots 0 → (SourcePair S → Fin d → ℤ) :=
    fun κ p => κ.1 (slotNode hS (Sum.inl p))
  have hmaps : Set.MapsTo Φ {κ : GenDecoration S d roots 0 |
        ∀ s, hasBond hS s → ‖base + latticePoint L (κ.1 (slotNode hS s)) - c s‖ ≤ 1}
      (↑(Fintype.piFinset Bnd) : Set (SourcePair S → Fin d → ℤ)) := by
    intro κ hκ
    simp only [Finset.mem_coe, Fintype.mem_piFinset]
    intro p
    by_cases hb : hasBond hS (Sum.inl p)
    · simp only [Bnd, hb, ite_true]
      apply hFmem
      have := hκ _ hb
      have e : (base - c (Sum.inl p)) + latticePoint L (κ.1 (slotNode hS (Sum.inl p))) =
          base + latticePoint L (κ.1 (slotNode hS (Sum.inl p))) - c (Sum.inl p) := by abel
      rw [e]; exact this
    · simp only [Bnd, hb, ite_false, Finset.mem_singleton]
      exact kconstInt_spec hS roots _ hb κ.1 κ.2.1.2 κ.2.2.1
  have hinj : Set.InjOn Φ {κ : GenDecoration S d roots 0 |
        ∀ s, hasBond hS s → ‖base + latticePoint L (κ.1 (slotNode hS s)) - c s‖ ≤ 1} := by
    intro κ _ κ' _ h
    apply Subtype.ext
    refine Comb.decoration_ext κ.2.1 κ'.2.1 fun ℓ => ?_
    rw [dec_leaf_eq_first hS κ.1 κ.2.1.2 ℓ, dec_leaf_eq_first hS κ'.1 κ'.2.1.2 ℓ]
    exact congrFun h (pairOfLeaf S hS ℓ)
  have hfin : (↑(Fintype.piFinset Bnd) : Set (SourcePair S → Fin d → ℤ)).Finite := Finset.finite_toSet _
  refine ⟨Set.Finite.of_injOn hmaps hinj hfin, (Set.ncard_le_ncard_of_injOn Φ hmaps hinj hfin).trans ?_⟩
  rw [Set.ncard_coe_finset, Fintype.card_piFinset]
  calc ∏ p, (Bnd p).card ≤ ∏ _p : SourcePair S, (⌊2 * L⌋₊ + 2) ^ d := by
        refine Finset.prod_le_prod fun p _ => ?_
        by_cases hb : hasBond hS (Sum.inl p)
        · simp only [Bnd, hb, ite_true]; exact hFcard p
        · simp only [Bnd, hb, ite_false, Finset.card_singleton]
          exact Nat.one_le_pow _ _ (by omega)
    _ = _ := by simp

end WaveTurbulence.Represents
