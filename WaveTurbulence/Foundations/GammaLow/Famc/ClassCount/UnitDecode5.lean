/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5c port (item I, with L5a tool) of main `WaveTurbulence.Foundations.Stage1.ClassCount.UnitDecode5` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitCodes
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitDecode4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitDecode5
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.UnitFamily


/-!
# CLASSCOUNT: runs of a block around an ingredient are Fama.unique

(a) `SourceVine.Chain` is `Src.Chain γ`; (b) a connected group meeting a sub-block `R ⊆ S` (one of whose joints is a
joint of `S` and the other is outside the group) lies inside `R` (`conn_subset_block`); (c) hence the run `L₀` of a
`SkelDecomp` equals the run `L` of `Fama.ingredient_runs` (`left_run_eq`, `right_run_eq`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.ClassCount WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.GammaLow.Fama WaveTurbulence.GammaLow.Famc.ClassCount WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.GammaLow.FinalCount

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant] [Fact TVineStructInputs]

theorem chain_of_source {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain γ M S a b n) : Src.Chain γ M S a b n := by
  induction h with
  | single hv => exact Src.Chain.single hv
  | append _ hT hi hne ih => exact Src.Chain.append ih hT hi hne

/-- A group-connected set meeting a sub-block `R ⊆ S` lies in `R`, provided that no atom of the group is a joint
of `R` that is not a joint of `S`. -/




theorem side_sub_right (N : Molecule V D) (hN : N.IsMolecule) {S A P P' Q' : Finset V} {a b x y : V}
    (hSB : N.IsBlock S a b) (hA : N.IsBlock A x y) (hPB : N.IsBlock P y b) (hPI : P ∩ A = {y})
    (hPS : P ⊆ S) (hS' : S = Q' ∪ A ∪ P') (hyP' : y ∈ P')
    (hQ' : Q' = ∅ ∨ (x ≠ a ∧ N.IsBlock Q' a x ∧ Q' ∩ A = {x})) : P ⊆ P' := by
  intro v hv
  have hvS : v ∈ Q' ∪ A ∪ P' := hS' ▸ hPS hv
  have hxy : x ≠ y := hA.2.2.2.1
  rcases Finset.mem_union.mp hvS with h | hvP'
  · rcases Finset.mem_union.mp h with hvQ | hvA
    · rcases hQ' with rfl | ⟨hxa, hQB, hQI⟩
      · simp at hvQ
      · have hxP : x ∉ P := by
          intro hx
          have : x ∈ P ∩ A := Finset.mem_inter.mpr ⟨hx, hA.2.1⟩
          rw [hPI, Finset.mem_singleton] at this
          exact hxy this
        have hQS : Q' ⊆ S := by rw [hS']; exact Finset.subset_union_left.trans Finset.subset_union_left
        have hsub := conn_subset_block N hN hSB hQS hQB (Or.inl rfl) (Or.inr (Or.inr hxP))
          hPB.2.2.2.2.2.2.2.2.2 hPS hv hvQ
        have hyQ : y ∈ Q' := hsub hPB.2.1
        have : y ∈ Q' ∩ A := Finset.mem_inter.mpr ⟨hyQ, hA.2.2.1⟩
        rw [hQI, Finset.mem_singleton] at this
        exact absurd this.symm hxy
    · have : v ∈ P ∩ A := Finset.mem_inter.mpr ⟨hv, hvA⟩
      rw [hPI, Finset.mem_singleton] at this
      exact this ▸ hyP'
  · exact hvP'

/-- The left run of a decomposition around `A` is Fama.unique. -/
theorem left_run_eq (N : Molecule V D) (hN : N.IsMolecule) {S A L0 R0 L R : Finset V} {a b x y : V}
    (hSB : N.IsBlock S a b) (hA : N.IsBlock A x y)
    (hS0 : S = L0 ∪ A ∪ R0) (hL0 : L0 = ∅ ∧ x = a ∨ (x ≠ a ∧ N.IsBlock L0 a x ∧ L0 ∩ A = {x}))
    (hR0 : R0 = ∅ ∨ (y ≠ b ∧ N.IsBlock R0 y b ∧ R0 ∩ A = {y}))
    (hS1 : S = L ∪ A ∪ R) (hL : L = ∅ ∧ x = a ∨ (x ≠ a ∧ N.IsBlock L a x ∧ L ∩ A = {x}))
    (hR : R = ∅ ∨ (y ≠ b ∧ N.IsBlock R y b ∧ R ∩ A = {y})) : L0 = L := by
  rcases hL0 with ⟨h0, hxa⟩ | ⟨hxa, hB0, hI0⟩
  · rcases hL with ⟨h1, -⟩ | ⟨hxa', -, -⟩
    · rw [h0, h1]
    · exact absurd hxa hxa'
  · rcases hL with ⟨-, hxa'⟩ | ⟨-, hB, hI⟩
    · exact absurd hxa' hxa
    · apply Finset.Subset.antisymm
      · exact side_sub_left N hN hSB hA hB0 hI0 (by rw [hS0]; exact Finset.subset_union_left.trans Finset.subset_union_left)
          hS1 hB.2.2.1 hR
      · exact side_sub_left N hN hSB hA hB hI (by rw [hS1]; exact Finset.subset_union_left.trans Finset.subset_union_left)
          hS0 hB0.2.2.1 hR0

/-- The right run of a decomposition around `A` is Fama.unique. -/
theorem right_run_eq (N : Molecule V D) (hN : N.IsMolecule) {S A L0 R0 L R : Finset V} {a b x y : V}
    (hSB : N.IsBlock S a b) (hA : N.IsBlock A x y)
    (hS0 : S = L0 ∪ A ∪ R0) (hL0 : L0 = ∅ ∨ (x ≠ a ∧ N.IsBlock L0 a x ∧ L0 ∩ A = {x}))
    (hR0 : R0 = ∅ ∧ y = b ∨ (y ≠ b ∧ N.IsBlock R0 y b ∧ R0 ∩ A = {y}))
    (hS1 : S = L ∪ A ∪ R) (hL : L = ∅ ∨ (x ≠ a ∧ N.IsBlock L a x ∧ L ∩ A = {x}))
    (hR : R = ∅ ∧ y = b ∨ (y ≠ b ∧ N.IsBlock R y b ∧ R ∩ A = {y})) : R0 = R := by
  rcases hR0 with ⟨h0, hyb⟩ | ⟨hyb, hB0, hI0⟩
  · rcases hR with ⟨h1, -⟩ | ⟨hyb', -, -⟩
    · rw [h0, h1]
    · exact absurd hyb hyb'
  · rcases hR with ⟨-, hyb'⟩ | ⟨-, hB, hI⟩
    · exact absurd hyb' hyb
    · apply Finset.Subset.antisymm
      · exact side_sub_right N hN hSB hA hB0 hI0
          (by rw [hS0]; exact Finset.subset_union_right) (by rw [hS1]) hB.2.1 hL
      · exact side_sub_right N hN hSB hA hB hI
          (by rw [hS1]; exact Finset.subset_union_right) (by rw [hS0]) hB0.2.1 hL0


end WaveTurbulence.GammaLow.Famc.ClassCount
