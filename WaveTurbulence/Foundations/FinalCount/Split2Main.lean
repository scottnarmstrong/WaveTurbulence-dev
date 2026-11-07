/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Split2Class2
public import WaveTurbulence.Foundations.FinalCount.Split2Arith
public import WaveTurbulence.Foundations.FinalCount.C4Route
public import WaveTurbulence.Foundations.FinalCount.Prop104TwoProved
public import WaveTurbulence.Foundations.FinalCount.ChainStruct
public import WaveTurbulence.Foundations.FinalCount.G8R.Step0Facts
public import WaveTurbulence.Foundations.FinalCount.G8R.ThmA
import Mathlib.Tactic

/-! # Case (4), two chains, `𝕄₁` not `Y`-exceptional and without a small cell (finalcount-g8, F6-1)

DH23 L1883-L1886: `𝔄₀ ≲ L^{-η/128}` for an even component with two `β`-atoms of degree two on separate chains,
when the closure `𝕄₁` is not `Y`-exceptional and no complete `(Y2)`-route of `𝕄₁` reaches a post molecule with at most
four atoms and a ladder cell.

The split `Q` of `prop104_two_proved` (`SplitBound`) is consumed at the level of decorations: the decorations of
`𝕄₀` with a good pair of multipliers whose transported decoration fails `Q` are counted by operation (d) twice
(`class1_bound`); the others by operation (d) on the first chain and operation (c) on the second one
(`class2_bound`).
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

theorem triple_of_tripSet {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] {N : Molecule V D}
    (h : (tripSet N).card ≤ 2) (p q r s t u' : V) (h1 : 3 ≤ N.bondsBetween p q) (h2 : 3 ≤ N.bondsBetween r s)
    (h3 : 3 ≤ N.bondsBetween t u') : s(p, q) = s(r, s) ∨ s(p, q) = s(t, u') ∨ s(r, s) = s(t, u') := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨n1, n2, n3⟩ := hne
  have hp : s(p, q) ∈ tripSet N := tripSet_iff.mpr ⟨p, q, rfl, h1⟩
  have hr : s(r, s) ∈ tripSet N := tripSet_iff.mpr ⟨r, s, rfl, h2⟩
  have ht : s(t, u') ∈ tripSet N := tripSet_iff.mpr ⟨t, u', rfl, h3⟩
  have hsub : ({s(p, q), s(r, s), s(t, u')} : Finset (Sym2 V)) ⊆ tripSet N := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have := card_le_card hsub
  rw [card_insert_of_notMem (by simp [n1, n2]), card_pair n3] at this
  omega

theorem bb_le_three_of_nonexc {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]
    {N : Molecule V D} (hR : RegCore N) (hnq : ¬ YReachesQT N) (p q : V) : N.bondsBetween p q ≤ 3 := by
  by_contra h
  push Not at h
  have hpq : p ≠ q := by
    rintro rfl
    rw [bondsBetween_self_eq_zero hR.loop] at h
    omega
  have hdeg : ∀ v ∈ N.atoms, N.deg v ≤ 4 := fun v hv => (hR.reg v hv).le
  have hQ := isQ_of_quadruple hdeg hR.conn hpq (by omega)
  exact hnq (YReachesQT.done _ (IsQ.bb_ne_three hQ) (Or.inl hQ))

theorem ofReal_sum_bound (A C e1 e2 T : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (h1 : 0 ≤ e1) (h2 : 0 ≤ e2)
    (h : A * (A * e1) + A * (C * e2) ≤ T) :
    ENNReal.ofReal A * (ENNReal.ofReal A * ENNReal.ofReal e1) +
      ENNReal.ofReal A * (ENNReal.ofReal C * ENNReal.ofReal e2) ≤ ENNReal.ofReal T := by
  have e : ENNReal.ofReal A * (ENNReal.ofReal A * ENNReal.ofReal e1) +
      ENNReal.ofReal A * (ENNReal.ofReal C * ENNReal.ofReal e2) =
        ENNReal.ofReal (A * (A * e1) + A * (C * e2)) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hA, ENNReal.ofReal_mul hA,
      ENNReal.ofReal_mul hA, ENNReal.ofReal_mul hC]
  rw [e]; exact ENNReal.ofReal_le_ofReal h

end WaveTurbulence.FinalCountG8
