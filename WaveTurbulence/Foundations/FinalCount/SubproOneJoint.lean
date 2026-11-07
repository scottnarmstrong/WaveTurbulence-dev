/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SourcePairsMain
public import WaveTurbulence.Foundations.Spine.SourceDVUnion
public import WaveTurbulence.Foundations.Spine.SourceHyperAbsorb
public import WaveTurbulence.Foundations.Spine.SourceOneJointContradiction
public import WaveTurbulence.Foundations.Spine.SourceHyperBlockFalse
import Mathlib.Tactic

/-!
# S4-DISJ: one-joint union of a selected ordinary object with an arbitrary SG chain object

lg-spine's `one_joint_union_contradiction` / `one_joint_hyperblock_false` need both objects in the second collection, but use the
second one only through its small gap and its disjointness from `F`. Here the second object `Q` is an arbitrary ordinary chain object
with those two properties (copies of the lg-spine proofs with `hQm` replaced by `hQsg`, `hQF`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset

theorem one_joint_union_false' {w d : ℕ} (G : Garden w)
    (hM : G.molecule.IsMolecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {c0 : GBranch G.tree → Mom d}
    (hκ : G.molecule.IsDecoration L base c0 κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c0 v = 0)
    {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))} {collection : Set (Object G.molecule)}
    (hc : IsSourceSecondCollection G L γ η base κ F omitted collection)
    {P Q : Object G.molecule} (hPm : P ∈ collection)
    {cj : GBranch G.tree} {n m : ℕ}
    (hPvc : ∃ h, P.shape = .vc h) (hQvc : ∃ h, Q.shape = .vc h)
    (hPl : P.lower = cj) (hQu : Q.upper = cj)
    (hPch : Chain G.molecule P.atoms P.upper cj n) (hQch : Chain G.molecule Q.atoms cj Q.lower m)
    (hPQ : P.atoms ∩ Q.atoms = {cj}) (hU : G.molecule.IsBlock (P.atoms ∪ Q.atoms) P.upper Q.lower)
    (hQsg : Q.HasGapKind L γ η base κ .SG) (hQF : Disjoint (↑Q.atoms : Set (GBranch G.tree)) F) :
    False := by
  obtain ⟨hPsg, hPel⟩ := ((hc.2.2 P).mp hPm).1
  rcases hPel with ⟨C, hPC, hCk, hCF⟩ | ⟨D, hD, hDF⟩
  · have hsub : P.atoms ⊆ C.atoms := hPC
    by_cases hCvc : ∃ h, C.shape = .vc h
    · exact one_joint_union_contradiction_vc_container G hM hκ hc0 hc hPm hPvc hQvc hCvc hPl hQu
        hPch hQch hPQ hU hPsg hQsg hCF (Or.inl hsub) hCk
    · have hCh : ∃ R, C.shape = .hyper R := by
        rcases hh : C.shape with h | R
        · exact absurd ⟨h, hh⟩ hCvc
        · exact ⟨R, rfl⟩
      exact one_joint_union_contradiction_hyper_container G hM hc hPm hPvc hQvc hCh hPl hQu
        hPch hQch hPQ hU hPsg hCF (Or.inl hsub) hCk
  · exact one_joint_tail_false hc hPm hPvc hQvc hPl hQu hPch hQch hPQ hU
      (union_eligible_of_dv_container G hM hPvc hQvc hPl hQu hPch hQch hPQ hU hPsg D hD hDF hQF)


theorem one_joint_hyperblock_false' {w d : ℕ} (G : Garden w)
    (hM : G.molecule.IsMolecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {c0 : GBranch G.tree → Mom d}
    (hκ : G.molecule.IsDecoration L base c0 κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c0 v = 0)
    {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))} {collection : Set (Object G.molecule)}
    (hc : IsSourceSecondCollection G L γ η base κ F omitted collection)
    {P Q : Object G.molecule} (hPm : P ∈ collection)
    {cj : GBranch G.tree} {n m : ℕ}
    (hPvc : ∃ h, P.shape = .vc h) (hQvc : ∃ h, Q.shape = .vc h)
    (hPl : P.lower = cj) (hQu : Q.upper = cj)
    (hPch : Chain G.molecule P.atoms P.upper cj n) (hQch : Chain G.molecule Q.atoms cj Q.lower m)
    (hPQ : P.atoms ∩ Q.atoms = {cj})
    (hH : Mole.IsHyperBlock G.molecule (P.atoms ∪ Q.atoms) P.upper Q.lower)
    (hQsg : Q.HasGapKind L γ η base κ .SG) (hQF : Disjoint (↑Q.atoms : Set (GBranch G.tree)) F) : False := by
  obtain ⟨hPsg, hPel⟩ := ((hc.2.2 P).mp hPm).1
  have hPB0 := object_vc_block P hPvc
  have hQB0 := object_vc_block Q hQvc
  obtain ⟨U, hUat, hUu, hUl, ⟨RU, hUsh, hUends, hUB⟩, hUgap⟩ :=
    hyper_union_object hPl hQu hPch hQch hPQ hPB0 hQB0 hH
  obtain ⟨rP, hrP, hkP⟩ := (object_vc_hasGapKind_iff P hPvc L γ η base κ .SG).mp hPsg
  have hUsg : U.HasGapKind L γ η base κ .SG := hUgap L γ η base κ .SG ⟨rP, hrP, hkP⟩
  have hbP : Q.lower ∉ P.atoms := by
    intro h
    have : Q.lower ∈ P.atoms ∩ Q.atoms := mem_inter.mpr ⟨h, hQB0.2.2.1⟩
    rw [hPQ] at this
    exact hQB0.2.2.2.1 (hQu.trans (mem_singleton.mp this).symm)
  have hUel : eligibleSecondObject G L γ η base κ F U := by
    refine ⟨hUsg, ?_⟩
    rcases one_joint_union_contained G hM hκ hc0 hPvc hQvc hPl hQu hPQ hPsg hQsg hQF hPel with
      ⟨C, hCk, hsub, hCvc, hCF⟩ | ⟨C, hCk, hsub, ⟨RC, hCsh⟩, hCF⟩ | ⟨D, hD, hDF⟩
    · exact Or.inl ⟨C, hUat ▸ hsub, hCk, hCF⟩
    · exact Or.inl ⟨C, hUat ▸ hsub, hCk, hCF⟩
    · exact Or.inr ⟨D, hUat ▸ hD, hDF⟩
  have hUo : U.atoms ∉ omitted := by
    intro ho
    obtain ⟨D, _, _, _, hS⟩ := hc.1 _ ho
    have hdeg := (Mole.hyperBlock_degrees G.molecule ⟨RU.added, hUends, hUB⟩).1
    have hUa : P.upper ∈ P.atoms ∪ Q.atoms := mem_union_left _ hPB0.2.1
    have hvine : ∀ {S : Finset (GBranch G.tree)} {x y : GBranch G.tree},
        G.molecule.IsVine .V S x y → U.atoms = S → False := by
      intro S x y hV hS
      rw [hUat] at hS
      rw [hS] at hdeg hUa
      obtain ⟨_, _, _, _, _, _, _, _, hint⟩ := hV.1
      by_cases h1 : P.upper = x
      · have := (Mole.block_joint_degrees G.molecule hV.1).1
        rw [← h1] at this; omega
      · by_cases h2 : P.upper = y
        · have := (Mole.block_joint_degrees G.molecule hV.1).2
          rw [← h2] at this; omega
        · have := hint.1 _ hUa h1 h2
          omega
    rcases hS with h | h
    · exact hvine D.first_vine h
    · exact hvine D.second_vine h
  have hcont := ((hc.2.2 P).mp hPm).2.2 U hUel hUo (isContained_of_vc_left P U hPvc (hUat ▸ subset_union_left))
  have hsub : U.atoms ⊆ P.atoms := Object.contained_atoms_subset U P hcont
  have hl : Q.lower ∈ P.atoms ∩ Q.atoms :=
    mem_inter.mpr ⟨hsub (hUat ▸ mem_union_right _ hQB0.2.2.1), hQB0.2.2.1⟩
  rw [hPQ] at hl
  exact hQB0.2.2.2.1 ((hQu.trans (mem_singleton.mp hl).symm))


end WaveTurbulence.Subpro
