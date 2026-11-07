/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBIncidenceSigns
public import WaveTurbulence.Foundations.FinalCount.AppBLargeGap
import Mathlib.Tactic

/-! # Transporting source LG to local outgoing bond labels -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbIncidenceDart (M : Molecule V D) (v : V) (x : D) : D :=
  if M.atom x = v then x else M.mate x

theorem appbIncidenceDart_atom (M : Molecule V D) (v : V) (x : D)
    (hx : appbIncidence M v x = 1) : M.atom (appbIncidenceDart M v x) = v := by
  by_cases h : M.atom x = v
  · simp [appbIncidenceDart,h]
  · have hh : M.atom (M.mate x) = v := by
      by_contra hn
      simp [appbIncidence,h,hn] at hx
    simp [appbIncidenceDart,h,hh]

/-- The source LG premise gives the physical gap in outgoing local labels
whenever their actual incidence signs differ. -/
theorem appb_incidence_large_gap (M : Molecule V D) {d : ℕ} (L : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) (g : ℝ) (hκ : ∀ x,κ (M.mate x) = κ x)
    (hLG : AppbLargeGap M L w κ g) {v : V} (hv : v ∈ M.atoms) {x y : D}
    (hx : appbIncidence M v x = 1) (hy : appbIncidence M v y = 1)
    (hox : M.out x = true) (hoy : M.out y = true) (hne : x ≠ y)
    (hsign : appbIncidenceSign M v x ≠ appbIncidenceSign M v y) :
    g ≤ ‖Molecule.kvec L w κ x-Molecule.kvec L w κ y‖ := by
  let x' := appbIncidenceDart M v x
  let y' := appbIncidenceDart M v y
  have hx' : x' ∈ M.dartsAt v := mem_filter.mpr ⟨mem_univ _,appbIncidenceDart_atom M v x hx⟩
  have hy' : y' ∈ M.dartsAt v := mem_filter.mpr ⟨mem_univ _,appbIncidenceDart_atom M v y hy⟩
  have hdir : M.out x' ≠ M.out y' := by
    by_cases ha : M.atom x = v <;> by_cases hb : M.atom y = v
    all_goals simp [appbIncidenceSign,ha,hb] at hsign
    all_goals simp [x',y',appbIncidenceDart,ha,hb,M.out_mate,hox,hoy]
  have hmate : y' ≠ M.mate x' := by
    by_cases ha : M.atom x = v <;> by_cases hb : M.atom y = v
    all_goals simp [x',y',appbIncidenceDart,ha,hb,M.mate_mate]
    · intro he
      have hh := congrArg M.out he
      simp [M.out_mate,hox,hoy] at hh
    · exact fun he => hne (mate_injective M he).symm
    · exact Ne.symm hne
    · intro he
      have hh := congrArg M.out he
      simp [M.out_mate,hox,hoy] at hh
  have hb := hLG v hv x' hx' y' hy' hdir hmate
  have hlabel (z : D) : Molecule.kvec L w κ (appbIncidenceDart M v z) = Molecule.kvec L w κ z := by
    unfold appbIncidenceDart
    split
    · rfl
    · simp only [Molecule.kvec,hκ]
  simpa only [x',y',hlabel] using hb

end WaveTurbulence.Mole
