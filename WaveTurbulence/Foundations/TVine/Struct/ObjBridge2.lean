/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.ObjBridge
import Mathlib.Tactic

/-!
# `Src.Object` ↔ `SubObj`: vine-likeness and member types (packet L3)

* `suOf U`: the sub-object `(S(U), upper, lower, hyper?)` of an `Src.Object`;
* `chainU_of_chain`, **`vineLike_suOf`**: for `γ ≤ 1/2`, an `Src.Object` inside a block `S` is a vine-like sub-object of
  `groupGraph M S`;
* `ingredient_I`: an (I) ingredient is a double bond;
* **`memberType_of_kinds`**: inside a T-vine, allowed kinds give L6's `TVineMemberType`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core GammaLow.FinalCount

universe u v

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The sub-object of an `Src.Object`. -/
def suOf {γ : ℝ} {M : Molecule V D} (U : Src.Object γ M) : SubObj V :=
  ⟨U.atoms, U.upper, U.lower, match U.shape with | .vc _ => false | .hyper _ => true⟩

theorem groupGraph_mult_ne_zero_of_dart (M : Molecule V D) {S : Finset V} {x : D} (hx : M.InGroup S x) :
    (groupGraph M S).mult (M.ends x) ≠ 0 := by
  rw [groupGraph_mult_eq_card, Finset.card_ne_zero]
  by_cases ho : M.out x = true
  · exact ⟨x, Finset.mem_filter.mpr ⟨(mem_groupDarts M).mpr ⟨ho, hx.1, hx.2⟩, rfl⟩⟩
  · refine ⟨M.mate x, Finset.mem_filter.mpr ⟨(mem_groupDarts M).mpr ⟨by rw [M.out_mate]; simpa using ho, hx.2,
      by rw [M.mate_mate]; exact hx.1⟩, ?_⟩⟩
    simp only [Molecule.ends, M.mate_mate]; exact Sym2.eq_swap

/-- A member of `𝒱_γ` (`γ ≤ 1/2`) has a kind. -/
theorem kind_of_isSomeVine {V' D' : Type*} [DecidableEq V'] [Fintype D'] [DecidableEq D'] {γ : ℝ} (hγ : γ ≤ 1 / 2)
    {M : Molecule V' D'} {T : Finset V'} {a b : V'} (h : Src.IsSomeVine γ M T a b) :
    M.IsBlock T a b ∧ ∃ k, IsVineKindU k (groupGraph M T) a b := by
  rcases h with ⟨-, hE⟩ | ⟨hgt, -⟩
  · obtain ⟨hB, hU⟩ := (isVineEnl_iff M).mp hE
    refine ⟨hB, ?_⟩
    rcases hU with h | h | h
    · exact ⟨.I, h⟩
    · exact ⟨.II, h⟩
    · exact ⟨.T, h⟩
  · exfalso; linarith

/-- **An `Src` chain is an L1 chain** inside the group graph of any superset. -/
theorem chainU_of_chain {V' D' : Type*} [DecidableEq V'] [Fintype D'] [DecidableEq D'] {γ : ℝ} (hγ : γ ≤ 1 / 2)
    {M : Molecule V' D'} {A T : Finset V'} {a b : V'} {n : ℕ} (h : Src.Chain γ M T a b n) (hTA : T ⊆ A) :
    ∃ ks, ChainU (groupGraph M A) T a b ks := by
  induction h with
  | @single S a b hv =>
    obtain ⟨-, k, hk⟩ := kind_of_isSomeVine hγ hv
    exact ⟨[k], ChainU.single (by rw [groupGraph_induce M hTA]; exact hk)⟩
  | @append S T a b c n h1 hv hST hac ih =>
    obtain ⟨ks, hks⟩ := ih (Finset.subset_union_left.trans hTA)
    obtain ⟨-, k, hk⟩ := kind_of_isSomeVine hγ hv
    exact ⟨ks ++ [k], ChainU.append hks
      (by rw [groupGraph_induce M (Finset.subset_union_right.trans hTA)]; exact hk) hST hac⟩

theorem core_suOf_vc {γ : ℝ} {M : Molecule V D} {S A : Finset V} {a b : V} (h : Src.IsVC γ M A a b)
    (hAS : A ⊆ S) : (suOf (⟨A, a, b, .vc h⟩ : Src.Object γ M)).core (groupGraph M S) = groupGraph M A := by
  show (if false = true then _ else induce (groupGraph M S) A) = _
  rw [if_neg (by decide), groupGraph_induce M hAS]

theorem core_suOf_hyper {γ : ℝ} {M : Molecule V D} {S A : Finset V} {a b : V}
    (R : Src.HyperLikeRealization γ M A a b) (hAS : A ⊆ S) :
    (suOf (⟨A, a, b, .hyper R⟩ : Src.Object γ M)).core (groupGraph M S) = groupGraph (M.eraseBond R.added) A := by
  have hB := R.adjoint.1
  have ha : a ∈ A := hB.2.1
  have hb : b ∈ A := hB.2.2.1
  have he : M.InGroup A R.added := by
    have := R.ends_eq
    simp only [Molecule.ends, Sym2.eq_iff] at this
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by rw [h1]; exact ha, by rw [h2]; exact hb⟩
    · exact ⟨by rw [h1]; exact hb, by rw [h2]; exact ha⟩
  show (if true = true then Core.eraseBond (induce (groupGraph M S) A) s(a, b) else _) = _
  rw [if_pos rfl, groupGraph_induce M hAS, groupGraph_eraseBond M he, R.ends_eq]

/-- **An `Src.Object` inside a block is a vine-like sub-object of the group graph** (`γ ≤ 1/2`). -/
theorem vineLike_suOf {γ : ℝ} (hγ : γ ≤ 1 / 2) {M : Molecule V D} {S : Finset V} (U : Src.Object γ M)
    (hUS : U.atoms ⊂ S) : ∃ ks, IsVineLikeU (groupGraph M S) (suOf U) ks := by
  obtain ⟨A, a, b, sh⟩ := U
  cases sh with
  | vc h =>
    have hAS : A ⊆ S := hUS.subset
    obtain ⟨n, hn⟩ := h.2
    obtain ⟨ks, hks⟩ := chainU_of_chain hγ hn (subset_refl A)
    refine ⟨ks, ⟨hUS, fun hh => by simp [suOf] at hh, ?_⟩, ?_⟩
    · rw [core_suOf_vc h hAS]; exact isBlockU_of_isBlock M h.1
    · rw [core_suOf_vc h hAS]; exact hks
  | hyper R =>
    have hAS : A ⊆ S := hUS.subset
    obtain ⟨n, hn⟩ := R.adjoint.2
    obtain ⟨ks, hks⟩ := chainU_of_chain hγ hn (subset_refl A)
    have hB := R.adjoint.1
    have he : M.InGroup S R.added := by
      have := R.ends_eq
      simp only [Molecule.ends, Sym2.eq_iff] at this
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by rw [h1]; exact hAS hB.2.1, by rw [h2]; exact hAS hB.2.2.1⟩
      · exact ⟨by rw [h1]; exact hAS hB.2.2.1, by rw [h2]; exact hAS hB.2.1⟩
    refine ⟨ks, ⟨hUS, fun _ => ?_, ?_⟩, ?_⟩
    · show (groupGraph M S).mult s(a, b) ≠ 0
      rw [← R.ends_eq]; exact groupGraph_mult_ne_zero_of_dart M he
    · rw [core_suOf_hyper R hAS]; exact isBlockU_of_isBlock _ hB
    · rw [core_suOf_hyper R hAS]; exact hks

end WaveTurbulence.TVine.Struct
