/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.WeylSupremum
public import Mathlib.Data.Fintype.Pi

/-! # Finite lattice boxes for compact cutoff sums -/

public section
open Finset
open scoped BigOperators
namespace WaveTurbulence.WeylSums

/-- The finite box containing the support of every coordinate cutoff. -/
@[expose] noncomputable def latticeBox (L : ℝ) (m : ℕ) : Finset (Fin m → ℤ) :=
  Fintype.piFinset (fun _ => Icc (-⌈L⌉ : ℤ) ⌈L⌉)

theorem sum_latticeBox (L : ℝ) (m : ℕ) (f : (Fin m → ℤ) → ℂ) :
    (∑ n ∈ latticeBox L m, f n) =
      ∑ v : Fin m → ↥(Icc (-⌈L⌉ : ℤ) ⌈L⌉), f (fun i => (v i : ℤ)) := by
  classical
  symm
  apply sum_bij (fun v _ => fun i => (v i : ℤ))
  · intro v hv
    exact Fintype.mem_piFinset.mpr (fun i => (v i).property)
  · intro v hv w hw heq
    funext i
    exact Subtype.ext (congrFun heq i)
  · intro n hn
    refine ⟨fun i => ⟨n i, Fintype.mem_piFinset.mp hn i⟩, mem_univ _, rfl⟩
  · intro v hv
    rfl

/-- Outside the displayed integer interval the coordinate cutoff vanishes. -/
theorem weylCutoff_eq_zero_of_not_mem {L : ℝ} (hL : 0 < L) (n : ℤ)
    (hn : n ∉ Icc (-⌈L⌉ : ℤ) ⌈L⌉) : weylCutoff ((n : ℝ)/L) = 0 := by
  apply Complex.ofReal_eq_zero.mpr
  apply Fourier.chi0_eq_zero
  by_contra hh
  have ha := abs_lt.mp (lt_of_not_ge hh)
  have hlo : -L < (n : ℝ) := by
    have := (lt_div_iff₀ hL).mp ha.1
    linarith
  have hhi : (n : ℝ) < L := by simpa only [one_mul] using (div_lt_iff₀ hL).mp ha.2
  apply hn
  apply mem_Icc.mpr
  have hc := Int.le_ceil L
  constructor
  · exact_mod_cast (by push_cast; linarith : ((-⌈L⌉ : ℤ) : ℝ) ≤ (n : ℝ))
  · exact_mod_cast hhi.le.trans hc

end WaveTurbulence.WeylSums
