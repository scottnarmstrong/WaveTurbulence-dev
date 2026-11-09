/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.DerivePlace

/-!
# Derivation of the cell decomposition, VII: the port bond at an atom

For a two-bond port `pt` of a region `X` and a piece `C` next to it, the two bonds of `pt` end at two distinct atoms
`u ≠ w` of `C`. For an **input** port (`C` outside `X`) the `C`-ends are `hd pt.out` and `tl pt.inn`; for an
**output** port (`C` inside `X`) they are `tl pt.out` and `hd pt.inn`. `inAt pt u`, `outAt pt u` pick the bond at
`u`; their two values are distinct, cross `X`, and have opposite orientation bits.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S : Finset V} {a b : V}
  {X : Finset V}

/-- The `C`-ends of an input port are `u, w`. -/
def InEnds (pt : Port2 M S X a b) (u w : V) : Prop :=
  (hd pt.out = u ∧ tl pt.inn = w) ∨ (hd pt.out = w ∧ tl pt.inn = u)

/-- The `C`-ends of an output port are `u, w`. -/
def OutEnds (pt : Port2 M S X a b) (u w : V) : Prop :=
  (tl pt.out = u ∧ hd pt.inn = w) ∨ (tl pt.out = w ∧ hd pt.inn = u)

/-- The input-port bond at `u`. -/
noncomputable def inAt (pt : Port2 M S X a b) (u : V) : Bond M S := if hd pt.out = u then pt.out else pt.inn

/-- The output-port bond at `u`. -/
noncomputable def outAt (pt : Port2 M S X a b) (u : V) : Bond M S := if tl pt.out = u then pt.out else pt.inn

theorem InEnds.symm {pt : Port2 M S X a b} {u w : V} (h : InEnds pt u w) : InEnds pt w u := by
  unfold InEnds at *; tauto

theorem OutEnds.symm {pt : Port2 M S X a b} {u w : V} (h : OutEnds pt u w) : OutEnds pt w u := by
  unfold OutEnds at *; tauto

theorem inAt_cross (pt : Port2 M S X a b) (u : V) : Crosses X (inAt pt u) := by
  unfold Crosses inAt
  split_ifs
  · exact Or.inl ⟨pt.out_tl, pt.out_hd⟩
  · exact Or.inr ⟨pt.inn_hd, pt.inn_tl⟩

theorem outAt_cross (pt : Port2 M S X a b) (u : V) : Crosses X (outAt pt u) := by
  unfold Crosses outAt
  split_ifs
  · exact Or.inl ⟨pt.out_tl, pt.out_hd⟩
  · exact Or.inr ⟨pt.inn_hd, pt.inn_tl⟩

section In

variable {pt : Port2 M S X a b} {u w : V} (huw : u ≠ w) (hE : InEnds pt u w)
include huw hE

/-- The input bond at `u` enters `C` at `u` from `X`, or leaves `C` at `u` into `X`. -/
theorem inAt_end : (hd (inAt pt u) = u ∧ tl (inAt pt u) ∈ X) ∨ (tl (inAt pt u) = u ∧ hd (inAt pt u) ∈ X) := by
  unfold inAt
  rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1]; exact Or.inl ⟨h1, pt.out_tl⟩
  · rw [if_neg (by rw [h1]; exact huw.symm)]; exact Or.inr ⟨h2, pt.inn_hd⟩

theorem inAt_ne : inAt pt u ≠ inAt pt w := by
  unfold inAt
  rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, if_neg (by rw [h1]; exact huw)]; exact pt.ne
  · rw [if_neg (by rw [h1]; exact huw.symm), if_pos h1]; exact pt.ne.symm

theorem inAt_bits : decide (tl (inAt pt u) = u) ≠ decide (tl (inAt pt w) = w) := by
  unfold inAt
  rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, if_neg (by rw [h1]; exact huw)]
    have : tl pt.out ≠ u := by
      intro h; have h3 := pt.out_tl; have h4 := pt.out_hd; rw [h] at h3; rw [h1] at h4; exact h4 h3
    simp [this, h2]
  · rw [if_neg (by rw [h1]; exact huw.symm), if_pos h1]
    have : tl pt.out ≠ w := by
      intro h; have h3 := pt.out_tl; have h4 := pt.out_hd; rw [h] at h3; rw [h1] at h4; exact h4 h3
    simp [this, h2]

end In

section Out

variable {pt : Port2 M S X a b} {u w : V} (huw : u ≠ w) (hE : OutEnds pt u w)
include huw hE

/-- The output bond at `u` leaves `C` at `u` out of `X`, or enters `C` at `u` from outside `X`. -/
theorem outAt_end : (tl (outAt pt u) = u ∧ hd (outAt pt u) ∉ X) ∨ (hd (outAt pt u) = u ∧ tl (outAt pt u) ∉ X) := by
  unfold outAt
  rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1]; exact Or.inl ⟨h1, pt.out_hd⟩
  · rw [if_neg (by rw [h1]; exact huw.symm)]; exact Or.inr ⟨h2, pt.inn_tl⟩

theorem outAt_ne : outAt pt u ≠ outAt pt w := by
  unfold outAt
  rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, if_neg (by rw [h1]; exact huw)]; exact pt.ne
  · rw [if_neg (by rw [h1]; exact huw.symm), if_pos h1]; exact pt.ne.symm

theorem outAt_bits : decide (tl (outAt pt u) = u) ≠ decide (tl (outAt pt w) = w) := by
  unfold outAt
  rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, if_neg (by rw [h1]; exact huw)]
    have : tl pt.inn ≠ w := by intro h; have := pt.inn_tl; rw [h] at this; rw [← h2] at this; exact this pt.inn_hd
    simp [h1, this]
  · rw [if_neg (by rw [h1]; exact huw.symm), if_pos h1]
    have : tl pt.inn ≠ u := by intro h; have := pt.inn_tl; rw [h] at this; rw [← h2] at this; exact this pt.inn_hd
    simp [h1, this]

end Out

/-- Counting a pair of stubs of one role with opposite bits. -/
theorem pair_count {n : ℕ} (role : Fin n → SRole) (ρ : SRole) (i j : Fin n) (hij : i ≠ j)
    (hrole : ∀ l, role l = ρ ↔ l = i ∨ l = j) (bits : Fin n → Bool) (h : bits i ≠ bits j) :
    (univ.filter fun l => role l = ρ ∧ bits l = true).card = (univ.filter fun l => role l = ρ ∧ bits l = false).card := by
  have hc : ∀ c : Bool, (univ.filter fun l => role l = ρ ∧ bits l = c) =
      (({i, j} : Finset (Fin n)).filter fun l => bits l = c) := by
    intro c; ext l; simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, hrole]
  rw [hc, hc, filter_insert, filter_insert, filter_singleton, filter_singleton]
  cases hi : bits i <;> cases hj : bits j <;> simp_all

/-- A role absent from a shape. -/
theorem absent_count {n : ℕ} (role : Fin n → SRole) (ρ : SRole) (hrole : ∀ l, role l ≠ ρ) (bits : Fin n → Bool) :
    (univ.filter fun l => role l = ρ ∧ bits l = true).card = (univ.filter fun l => role l = ρ ∧ bits l = false).card := by
  have e : ∀ c : Bool, (univ.filter fun l => role l = ρ ∧ bits l = c) = ∅ := by
    intro c; ext l; simp [hrole l]
  rw [e, e]

end WaveTurbulence.TVine.Chart
