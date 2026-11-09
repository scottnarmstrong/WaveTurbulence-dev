/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineDVOrdinaryRemoval
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVTypeIRemoval
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineDVOrdinaryRemoval`** (sha256 in H/COPIED-SHA256SUMS), **restated over the
low family by L6-HDS** (PLAN-L6 §3e–3f, layer H-DS). Main's DV is two vines (V); here it is the DV′ of D11
(`Src.IsDV Src.γL`), whose branches are T-vines with `σ = 1` (`H/DS/DV.lean`); the removal arguments are N3 Cor 1.16′(3) and
N3 Lemma P (proved by L3, L3-LP; `H/DS/Removal.lean`, `H/DS/RemovalDV.lean`). Low-range change: each removed ordinary vine is a whole T-vine branch or lies in one branch, disjoint from the other
(`vine_in_DV_branch_or_split`); without a branch piece: `DS.DV_split_removal_connected`; with one (disjointness allows at
most one): N3 Lemma P in the other branch (`DS.DV_branch_removal_connected`). The statement is main's.

# Removal of ordinary vines in a DV′ -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc, complete ordinary-removal clause for a DV′ of the low family. No decoration or SG premise is needed:
each removed ordinary vine is a whole branch or lies in one branch, and disjointness permits at most one branch removal. -/
theorem ordinary_vines_removal_in_DV_connected (M : Molecule V D) (hM : M.IsMolecule)
    {U : Finset V} {a b : V} (hU : Src.IsDV Src.γL M U a b) (ps : List (RemovalPiece V D))
    (hvine : ∀ P ∈ ps, Src.IsSomeVine Src.γL M P.atoms P.left P.right)
    (hsub : ∀ P ∈ ps, P.atoms ⊆ U)
    (hD : ∀ P ∈ ps, P.darts = univ.filter (M.InGroup P.atoms))
    (hdis : ∀ P ∈ ps, ∀ Q ∈ ps, P ≠ Q → Disjoint P.atoms Q.atoms) :
    ∀ u ∈ remainingAtoms U ps, ∀ v ∈ remainingAtoms U ps, (removeBlocks M U ps).SameComponent u v := by
  classical
  obtain ⟨S, T, hσ, hS, hT, hi, rfl⟩ := DS.dv_branches hU
  have hreal : ∀ P ∈ ps, ∃ O : Src.Object Src.γL M, DS.Realizes O P := by
    intro P hP
    refine ⟨Src.Object.ofVine (hvine P hP), rfl, rfl, rfl, fun x => ?_⟩
    rw [hD P hP]
    exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨mem_univ _, h⟩⟩
  have hcls := fun P (hP : P ∈ ps) => vine_in_DV_branch_or_split M hM hσ hS hT hi (hvine P hP) (hsub P hP)
  have hjoints : ∀ P ∈ ps, ∀ B : Finset V, M.IsBlock B a b → P.atoms = B →
      (P.left = a ∧ P.right = b) ∨ (P.left = b ∧ P.right = a) := by
    intro P hP B hB hPB
    have hj := block_joints_unique M (hvine P hP).block (hPB ▸ hB)
    have hlr : P.left ≠ P.right := (hvine P hP).block.2.2.2.1
    have hl : P.left ∈ ({a, b} : Finset V) := by rw [← hj]; simp
    have hr : P.right ∈ ({a, b} : Finset V) := by rw [← hj]; simp
    simp only [mem_insert, mem_singleton] at hl hr
    rcases hl with hl | hl <;> rcases hr with hr | hr
    · exact absurd (hl.trans hr.symm) hlr
    · exact Or.inl ⟨hl, hr⟩
    · exact Or.inr ⟨hl, hr⟩
    · exact absurd (hl.trans hr.symm) hlr
  have hothers : ∀ (B C : Finset V) (P0 : RemovalPiece V D), P0 ∈ ps → P0.atoms = B → a ∈ B → b ∈ B →
      (∀ P ∈ ps, P.atoms = B ∨ P.atoms = C ∨ (P.atoms ⊆ B ∧ Disjoint P.atoms C) ∨ (P.atoms ⊆ C ∧ Disjoint P.atoms B)) →
      a ∈ C → ∀ P ∈ ps, P ≠ P0 → P.atoms ⊆ C ∧ a ∉ P.atoms ∧ b ∉ P.atoms := by
    intro B C P0 hP0 hP0B haB hbB hc haC P hP hne
    have hd := hdis P0 hP0 P hP (Ne.symm hne)
    rw [hP0B] at hd
    have haP : a ∉ P.atoms := fun h => disjoint_left.mp hd haB h
    have hbP : b ∉ P.atoms := fun h => disjoint_left.mp hd hbB h
    have hl : P.left ∈ P.atoms := (hvine P hP).block.2.1
    refine ⟨?_, haP, hbP⟩
    rcases hc P hP with h | h | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact (haP (h ▸ haB)).elim
    · exact (haP (h ▸ haC)).elim
    · exact (disjoint_left.mp hd (h1 hl) hl).elim
    · exact h1
  by_cases hbr : ∃ P0 ∈ ps, P0.atoms = S ∨ P0.atoms = T
  · obtain ⟨P0, hP0, hP0e⟩ := hbr
    rcases hP0e with hP0S | hP0T
    · exact DS.DV_branch_removal_connected hM hσ hT hi ps P0 hP0 hP0S (hjoints P0 hP0 S hS.1 hP0S)
        (by rw [hD P0 hP0, hP0S]) (fun P hP _ => hreal P hP)
        (hothers S T P0 hP0 hP0S hS.1.2.1 hS.1.2.2.1 (fun P hP => hcls P hP) hT.1.2.1) hdis
    · rw [union_comm]
      exact DS.DV_branch_removal_connected hM hσ hS (by rw [inter_comm]; exact hi) ps P0 hP0 hP0T
        (hjoints P0 hP0 T hT.1 hP0T) (by rw [hD P0 hP0, hP0T]) (fun P hP _ => hreal P hP)
        (hothers T S P0 hP0 hP0T hT.1.2.1 hT.1.2.2.1
          (fun P hP => by rcases hcls P hP with h | h | h | h
                          · exact Or.inr (Or.inl h)
                          · exact Or.inl h
                          · exact Or.inr (Or.inr (Or.inr h))
                          · exact Or.inr (Or.inr (Or.inl h))) hS.1.2.1) hdis
  · push Not at hbr
    refine DS.DV_split_removal_connected hM hS hT ps hreal
      (fun P hP x hx => by rw [hD P hP] at hx; exact (mem_filter.mp hx).2) (fun P hP => ?_) hdis
    rcases hcls P hP with h | h | h | h
    · exact absurd h (hbr P hP).1
    · exact absurd h (hbr P hP).2
    · exact Or.inl h
    · exact Or.inr h

end WaveTurbulence.GammaLow.FinalCount.H
