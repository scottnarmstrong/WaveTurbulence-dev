/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.GaussianLattice
public import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-!
# Completing residue lattices

A residue class and an integer quotient enumerate the integers exactly once.
This merges the finitely many Poisson dual lattices into a single lattice of
spacing `1/q`, before applying the Gaussian tail estimate.
-/

public section

open scoped BigOperators
open Finset

namespace WaveTurbulence.WeylSums

/-- Residue representative plus denominator times quotient. -/
@[expose] noncomputable def residueLatticeEquiv (q : ℕ) [NeZero q] : (ZMod q × ℤ) ≃ ℤ :=
  Equiv.ofBijective (fun p => (p.1.val : ℤ) + q * p.2) (by
    constructor
    · rintro ⟨b, m⟩ ⟨c, n⟩ h
      have hbc : b = c := by
        have hh := congrArg (fun z : ℤ => (z : ZMod q)) h
        simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
          zero_mul, add_zero, ZMod.natCast_zmod_val] using hh
      subst c
      have hmn : m = n := mul_left_cancel₀ (by exact_mod_cast NeZero.ne q)
        (add_left_cancel h)
      exact Prod.ext rfl hmn
    · intro n
      obtain ⟨m, hm⟩ := (ZMod.intCast_eq_iff q n (n : ZMod q)).mp rfl
      exact ⟨⟨(n : ZMod q), m⟩, hm.symm⟩)

/-- Merging the dual Gaussian lattices from all residue frequencies. -/
theorem tsum_gaussian_residues_eq (q : ℕ) [NeZero q] (u : ℝ) {t : ℝ} (ht : 0 < t) :
    (∑ b : ZMod q, ∑' n : ℤ,
      Real.exp (-Real.pi * ((n : ℝ) + (b.val : ℝ) / q - u) ^ 2 * t)) =
      ∑' k : ℤ, Real.exp (-Real.pi * ((k : ℝ) - q * u) ^ 2 * (t / (q : ℝ) ^ 2)) := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  let f : ℤ → ℝ := fun k => Real.exp (-Real.pi * ((k : ℝ) - q * u) ^ 2 * (t / (q : ℝ) ^ 2))
  have hf : Summable f := summable_gaussian_lattice (q * u) (div_pos ht (sq_pos_of_pos hq))
  have hp : Summable (fun p : ZMod q × ℤ => f (residueLatticeEquiv q p)) :=
    hf.comp_injective (residueLatticeEquiv q).injective
  have hterm (b : ZMod q) (n : ℤ) : f (residueLatticeEquiv q (b, n)) =
      Real.exp (-Real.pi * ((n : ℝ) + (b.val : ℝ) / q - u) ^ 2 * t) := by
    dsimp [f, residueLatticeEquiv, Equiv.ofBijective]
    congr 1
    push_cast
    field_simp
    ring
  have heq := (residueLatticeEquiv q).tsum_eq f
  rw [hp.tsum_prod] at heq
  simpa only [hterm, tsum_fintype] using heq

end WaveTurbulence.WeylSums
