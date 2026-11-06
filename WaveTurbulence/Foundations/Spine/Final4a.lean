/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Final3f
public import WaveTurbulence.Foundations.Spine.MolecularSpineAt
import Mathlib.Tactic
/-! `LadderFourierAt P` from the analytic inequalities on the parameters (TARGET ladderl1old). -/
@[expose] public section
open WaveTurbulence.Induct
open Finset MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDisjoint
open scoped Classical

/-- The analytic inequalities on the parameters used in the proof. -/
structure LFHyps (P : WTParams) : Prop where
  d1 : 1 ≤ P.d
  Lpos : 0 < P.L
  δpos : 0 < P.δ
  δle : P.δ ≤ 1
  νnn : 0 ≤ P.ν
  Λ1 : 1 ≤ Real.log P.L
  big : Real.log P.L ^ 2 < 1 + P.δ * P.L ^ (2 * P.γ)
  Y : 3 * (2 * (2 * Real.arsinh (Mv P.d P.L) + 1)) ≤ 180 * P.d * Real.log P.L
  expb : Real.exp ((P.D : ℝ) * P.δ ^ (1 + 10 * P.ν) * Real.log P.L) * (Real.log P.L) ^ (2 * P.d + 4) ≤
    P.L ^ (P.δ ^ (5 * P.ν))
  ΛLam : (Real.log P.L) ^ 2 ≤ P.L ^ (P.δ ^ (5 * P.ν))
  free : 128 * (180 * P.d * Real.log P.L) ≤ P.L ^ (P.δ ^ (5 * P.ν))
  C : 128 * (180 * P.d) * (64 * (1 + P.d * (2 : ℝ) ^ (P.d - 1))) ≤ P.C₁
  C1 : 1 ≤ P.C₁

theorem ladder_fourier_param (P : WTParams) (h : LFHyps P) : LadderFourierAt P := by
  intro p hp R hR1 hR10 G hplain hirr hbal hord1 hord2 D scales hlayer hamp base roots
  have hDt0 : 0 ≤ (P.D : ℝ) := Nat.cast_nonneg _
  have hDt : ∀ v, (D.layer v : ℝ) + 1 ≤ (P.D : ℝ) := fun v => by
    have : D.layer v + 1 ≤ P.D := by have := hlayer v; omega
    exact_mod_cast this
  set Tr : ℝ := P.C₁ * ((P.C₁ * P.δ ^ (-1 / 2 - 5 * P.ν)) ^ G.order *
      (P.L ^ (P.δ ^ (5 * P.ν))) ^ G.molecule.rho *
      ∏ S ∈ G.molecule.maximalLadders, Molecule.ladderWeight P.L P.γ P.δ (scales S) ^ Molecule.ladderLength S)
    with hTr
  have hT : Tr = P.C₁ * (P.C₁ * P.δ ^ (-1 / 2 - 5 * P.ν)) ^ G.order *
      P.L ^ (P.δ ^ (5 * P.ν) * G.molecule.rho) *
      ∏ S ∈ G.molecule.maximalLadders, Molecule.ladderWeight P.L P.γ P.δ (scales S) ^ Molecule.ladderLength S := by
    rw [hTr, ← Real.rpow_natCast (P.L ^ (P.δ ^ (5 * P.ν))) G.molecule.rho, ← Real.rpow_mul h.Lpos.le]
    ring
  rw [← hT]
  have hB : ∀ (π0 : PF G) (A : Finset (GBranch G.tree)),
      ∫⁻ α in Wnb (clsPF G D scales P.L P.γ P.η P.δ base roots π0),
        ‖Phi (splicedTimeDomain G D.layer D.rootTime) (fun v => (D.layer v : ℝ)) A α‖ₑ ≤
      ENNReal.ofReal Tr / (((Sigs G).card : ℝ≥0∞) * 2 ^ (3 * G.order)) := by
    intro π0 A
    have hcard : ((Sigs G).card : ℝ≥0∞) ≠ 0 := by
      have : 0 < (Sigs G).card := Finset.card_pos.mpr ⟨π0.sig, π0.sig_mem⟩
      exact_mod_cast this.ne'
    rw [ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero hcard (by positivity)))
      (Or.inl (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by simp)))]
    rw [mul_comm]
    exact class_cond hplain h.Lpos D hamp scales P.γ P.η P.δ h.δpos h.δle P.ν h.νnn base roots (P.D : ℝ)
      (P.L ^ (P.δ ^ (5 * P.ν))) P.C₁ hDt0 hDt h.Λ1 h.big h.Y h.expb h.ΛLam h.free h.C h.C1 h.d1 π0 A
  refine (box_sum_bound hplain h.Lpos D scales P.γ P.η P.δ base roots _ hB).trans ?_
  have h8 : (2 : ℝ≥0∞) ^ Fintype.card (GBranch G.tree) * (2 ^ Fintype.card (GBranch G.tree) *
      (2 ^ Fintype.card (GBranch G.tree) * (ENNReal.ofReal Tr / (((Sigs G).card : ℝ≥0∞) * 2 ^ (3 * G.order))))) =
      2 ^ (3 * G.order) * (ENNReal.ofReal Tr / (((Sigs G).card : ℝ≥0∞) * 2 ^ (3 * G.order))) := by
    rw [card_branch_eq G, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
    congr 2; ring
  rw [h8, ← mul_assoc]
  exact ENNReal.mul_div_le

end WaveTurbulence.Ladder
