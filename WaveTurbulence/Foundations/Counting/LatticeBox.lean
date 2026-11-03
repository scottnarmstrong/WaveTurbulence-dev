/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.LatticeDisc
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Finite integer boxes with arbitrary real centers

Coordinate counting for DH23 `basiccount0pre` (2). The box is the actual
product of closed real integer intervals; centers are never rounded.
-/

public section

namespace WaveTurbulence.Counting

/-- The integer points in the closed coordinate box of half-width `L`. -/
@[expose] noncomputable def latticeBox {d : ℕ} (c : Fin d → ℝ) (L : ℝ) :
    Finset (Fin d → ℤ) := Fintype.piFinset (fun i => integerInterval (c i-L) (c i+L))

/-- Membership in the actual finite integer box. -/
theorem mem_latticeBox {d : ℕ} (n : Fin d → ℤ) (c : Fin d → ℝ) (L : ℝ) :
    n ∈ latticeBox c L ↔ ∀ i, |(n i:ℝ)-c i| ≤ L := by
  simp only [latticeBox,Fintype.mem_piFinset,mem_integerInterval,abs_le]
  constructor
  · intro h i
    have hi := h i
    constructor <;> linarith only [hi.1,hi.2]
  · intro h i
    have hi := h i
    constructor <;> linarith only [hi.1,hi.2]

/-- A closed real interval of length `2L` contains at most `2L+1` integers. -/
theorem card_integerInterval_le (c : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ((integerInterval (c-L) (c+L)).card:ℝ) ≤ 2*L+1 := by
  have hc := card_integerInterval_eq_sawtooth (l := c-L) (u := c+L) (by linarith only [hL])
  have h₁ := (abs_le.mp (NumberTheory.abs_sawtooth_le_half (c+L))).1
  have h₂ := (abs_le.mp (NumberTheory.abs_sawtooth_le_half (-(c-L)))).1
  linarith only [hc,h₁,h₂]

/-- The number of lattice points in an arbitrary translated box. -/
theorem card_latticeBox_le {d : ℕ} (c : Fin d → ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ((latticeBox c L).card:ℝ) ≤ (2*L+1)^d := by
  rw [latticeBox,Fintype.card_piFinset,Nat.cast_prod]
  calc
    _ ≤ ∏ _i : Fin d, (2*L+1) := Finset.prod_le_prod₀
      (fun i _ => Nat.cast_nonneg _) (fun i _ => card_integerInterval_le (c i) hL)
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]

/-- A finite family contained coordinatewise in a translated box has the
same cardinality bound. -/
theorem card_le_of_coordinate_bounds {d : ℕ} (s : Finset (Fin d → ℤ))
    (c : Fin d → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ n ∈ s, ∀ i, |(n i:ℝ)-c i| ≤ L) : (s.card:ℝ) ≤ (2*L+1)^d := by
  have hs : s ⊆ latticeBox c L := fun n hn => (mem_latticeBox n c L).mpr (h n hn)
  have hc : (s.card:ℝ) ≤ ((latticeBox c L).card:ℝ) := by exact_mod_cast Finset.card_le_card hs
  exact hc.trans (card_latticeBox_le c hL)

/-- A finite family of integer vectors has at most the product of the numbers
of choices for its individual coordinates. -/
theorem card_le_prod_card_coordinate_images {d : ℕ} (s : Finset (Fin d → ℤ)) :
    s.card ≤ ∏ i, (s.image (fun n => n i)).card := by
  classical
  have hs : s ⊆ Fintype.piFinset (fun i => s.image (fun n => n i)) := by
    intro n hn
    exact Fintype.mem_piFinset.mpr (fun i => Finset.mem_image_of_mem (fun n => n i) hn)
  have hc := Finset.card_le_card hs
  rw [Fintype.card_piFinset] at hc
  exact hc

end WaveTurbulence.Counting
