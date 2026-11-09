/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.Local

/-!
# Phase targets of the local charts (M4 Theorem C (C4), Prop L)

The exact phase forms required by the contract, as integer Gram matrices in the local variables, and the
decidable phase conditions of pair (2-atom piece) and core (3-atom piece) charts:
* pair, `s`-atom (local atom `0`): `−2⟨x, y⟩`; `t`-atom (local atom `1`): `2⟨x, y⟩ + 2⟨r, ζ₀x + ζ₁y + ζ₂r⟩`;
* core, `w_a` (atom `0`): `2σ₁⟨u₁, u₂⟩`; `w_b` (atom `1`): `2σ₁⟨u₁, u₃⟩` (linear) or
  `2σ₁σ₂⟨u₃, u₁ + u₂ − u₃⟩`; the sum over the three atoms: `2⟨r, ξ₀u₁ + ξ₁u₂ + ξ₂u₃ + ξ₃r⟩`.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset

/-- `−2⟨x, y⟩`. -/
def sTarget : Fin 3 → Fin 3 → ℤ := ![![0, -2, 0], ![0, 0, 0], ![0, 0, 0]]

/-- `2⟨x, y⟩ + 2⟨r, ζ₀x + ζ₁y + ζ₂r⟩`. -/
def tTarget (ζ : Fin 3 → ℤ) : Fin 3 → Fin 3 → ℤ :=
  ![![0, 2, 0], ![0, 0, 0], ![2 * ζ 0, 2 * ζ 1, 2 * ζ 2]]

/-- `2σ₁⟨u₁, u₂⟩`. -/
def aTarget (σ₁ : ℤ) : Fin 4 → Fin 4 → ℤ := ![![0, 2 * σ₁, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]

/-- `2σ₁⟨u₁, u₃⟩` or `2σ₁σ₂⟨u₃, u₁ + u₂ − u₃⟩`. -/
def bTarget (lin : Bool) (σ₁ σ₂ : ℤ) : Fin 4 → Fin 4 → ℤ :=
  if lin then ![![0, 0, 2 * σ₁, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
  else ![![0, 0, 0, 0], ![0, 0, 0, 0], ![2 * σ₁ * σ₂, 2 * σ₁ * σ₂, -2 * σ₁ * σ₂, 0], ![0, 0, 0, 0]]

/-- `2⟨r, ξ₀u₁ + ξ₁u₂ + ξ₂u₃ + ξ₃r⟩`. -/
def sumTarget (ξ : Fin 4 → ℤ) : Fin 4 → Fin 4 → ℤ :=
  ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![2 * ξ 0, 2 * ξ 1, 2 * ξ 2, 2 * ξ 3]]

/-- Unit coefficient (decidable form). -/
def IsUnitZ (z : ℤ) : Prop := z = 0 ∨ z = 1 ∨ z = -1

instance (z : ℤ) : Decidable (IsUnitZ z) := inferInstanceAs (Decidable (_ ∨ _))

/-- The number of local bonds joining the two local atoms of a pair chart. -/
def pairBonds {nB : ℕ} (c : LocalChart 2 2 nB) : ℕ :=
  (univ.filter fun l : Fin nB => (c.src l = some 0 ∧ c.dst l = some 1) ∨ (c.src l = some 1 ∧ c.dst l = some 0)).card

/-- **Pair phase conditions.** -/
def PairOK {nB : ℕ} (c : LocalChart 2 2 nB) : Prop :=
  c.gram 0 = sTarget ∧ c.gram 1 = tTarget c.ζ ∧ (∀ i, IsUnitZ (c.ζ i)) ∧ pairBonds c = c.mu ∧
    (c.mu = 1 ∨ c.mu = 2) ∧ (∀ l u, c.src l = some u → c.dst l ≠ some u)

instance {nB : ℕ} (c : LocalChart 2 2 nB) : Decidable (PairOK c) := by unfold PairOK; infer_instance

/-- **Core phase conditions.** -/
def CoreOK {nB : ℕ} (c : LocalChart 3 3 nB) : Prop :=
  c.gram 0 = aTarget c.σ₁ ∧ c.gram 1 = bTarget c.lin c.σ₁ c.σ₂ ∧
    (∀ i j, (c.gram 0 i j + c.gram 1 i j + c.gram 2 i j) + (c.gram 0 j i + c.gram 1 j i + c.gram 2 j i) =
      sumTarget c.ξ i j + sumTarget c.ξ j i) ∧
    (c.σ₁ = 1 ∨ c.σ₁ = -1) ∧ (c.σ₂ = 1 ∨ c.σ₂ = -1) ∧ (∀ i, IsUnitZ (c.ξ i)) ∧
    (∀ l u, c.src l = some u → c.dst l ≠ some u)

instance {nB : ℕ} (c : LocalChart 3 3 nB) : Decidable (CoreOK c) := by unfold CoreOK; infer_instance

/-! ## Meaning of the targets -/

section Meaning

variable {d : ℕ}

open LocalChart

theorem quad_sTarget (x y ρ : Mom d) : quad sTarget ![x, y, ρ] = -2 * inner ℝ x y := by
  simp [quad, sTarget, Fin.sum_univ_three]

theorem quad_tTarget (ζ : Fin 3 → ℤ) (x y ρ : Mom d) :
    quad (tTarget ζ) ![x, y, ρ] =
      2 * inner ℝ x y + 2 * inner ℝ ρ ((ζ 0 : ℝ) • x + (ζ 1 : ℝ) • y + (ζ 2 : ℝ) • ρ) := by
  simp only [quad, tTarget, Fin.sum_univ_three, inner_add_right, real_inner_smul_right]
  simp
  ring

theorem quad_aTarget (σ₁ : ℤ) (u₁ u₂ u₃ ρ : Mom d) :
    quad (aTarget σ₁) ![u₁, u₂, u₃, ρ] = 2 * (σ₁ : ℝ) * inner ℝ u₁ u₂ := by
  simp [quad, aTarget, Fin.sum_univ_four]

theorem quad_bTarget (lin : Bool) (σ₁ σ₂ : ℤ) (u₁ u₂ u₃ ρ : Mom d) :
    quad (bTarget lin σ₁ σ₂) ![u₁, u₂, u₃, ρ] =
      2 * (σ₁ : ℝ) * (if lin then inner ℝ u₁ u₃ else (σ₂ : ℝ) * inner ℝ u₃ (u₁ + u₂ - u₃)) := by
  cases lin
  · simp only [quad, bTarget, Fin.sum_univ_four, inner_add_right, inner_sub_right]
    simp
    ring
  · simp [quad, bTarget, Fin.sum_univ_four]

theorem quad_sumTarget (ξ : Fin 4 → ℤ) (u₁ u₂ u₃ ρ : Mom d) :
    quad (sumTarget ξ) ![u₁, u₂, u₃, ρ] =
      2 * inner ℝ ρ ((ξ 0 : ℝ) • u₁ + (ξ 1 : ℝ) • u₂ + (ξ 2 : ℝ) • u₃ + (ξ 3 : ℝ) • ρ) := by
  simp only [quad, sumTarget, Fin.sum_univ_four, inner_add_right, real_inner_smul_right]
  simp
  ring

/-- Sums of quadratic forms. -/
theorem quad_add {m : ℕ} (G H : Fin m → Fin m → ℤ) (z : Fin m → Mom d) :
    quad (fun i j => G i j + H i j) z = quad G z + quad H z := by
  simp only [quad, Int.cast_add, add_mul, Finset.sum_add_distrib]

end Meaning

end WaveTurbulence.TVine.Chart
