/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.LemmaP.Parity
import Mathlib.Tactic

/-!
# N3 Lemma P (parity) (packet L3-LP)

Source: N3 Lemma P (`research-gamma-half-3/NOTES.txt` L500–L511). Let `V = (S, j₁, j₂)` be a vine of `𝒱_enl` whose
joints are joined by the bond `f` (`σ = 1`), and let `F` be a family of pairwise disjoint sub-objects of `V`, none
containing `j₁` or `j₂`. Let `G` be `V` after removing `F` (sources' semantics, `remAdj`). If `G` is connected, so is
`G − f` (`remAdjWithout`).

Proof (N3's, in a form that needs no case split on the members):
* it suffices that `j₁` and `j₂` are joined in `G − f` (`eqvGen_without_of_joints`): a path of `G` through `f` is
  rerouted;
* otherwise let `X` be the atoms of `S` joined to `j₁` in `G − f`. The bonds of `S` leaving `X` are `f` and, for each
  member `U`, some bonds of `E(U°)`: a bond of `S` that is neither `f` nor in any `E(U°)` (a hyper member's kept
  adjoint included) is a bond of `G − f`, so it does not leave `X`;
* every cut of the block `S` is even, and so is every cut of `E(U°)` (the bonds of a block, or of the adjoint block of
  a hyper member: degrees 2 and 4) (`LemmaP.even_card_leaving`). The members are atom-disjoint, so their bond sets
  are disjoint, and `f` is in none of them (the members avoid the joints). Hence `1 + even = even`, a contradiction.

N3 instead enlarges `X` by the interiors of the members with upper joint in `X` and counts the split block members;
the parity identity is the same (N3: "|δ_V(X~)| = 1 + 2k is odd").
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset GammaLow.FinalCount

universe u v

namespace LemmaP

variable {V : Type*} {D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The two ends of a bond with `ends f = s(j₁, j₂)`, oriented: some dart `f₀` of the bond sits at `j₁`. -/
theorem exists_dart_at_j₁ {M : Molecule V D} {f : D} {j₁ j₂ : V} (hf : M.ends f = s(j₁, j₂)) :
    ∃ f₀ : D, (f₀ = f ∨ f₀ = M.mate f) ∧ M.atom f₀ = j₁ ∧ M.atom (M.mate f₀) = j₂ := by
  have h := Sym2.eq_iff.mp hf
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨f, Or.inl rfl, h1, h2⟩
  · exact ⟨M.mate f, Or.inr rfl, h2, by rw [M.mate_mate]; exact h1⟩

/-- A path of `G` becomes a path of `G − f` once the ends `j₁, j₂` of `f` are joined in `G − f`. -/
theorem eqvGen_without_of_joints {γ : ℝ} {M : Molecule V D} {S : Finset V} {j₁ j₂ : V} {f : D}
    (hf : M.ends f = s(j₁, j₂)) {n : ℕ} {U : Fin n → Src.Object γ M}
    (hj : Relation.EqvGen (remAdjWithout M S U f) j₁ j₂) {a b : V}
    (hab : Relation.EqvGen (remAdj M S U) a b) : Relation.EqvGen (remAdjWithout M S U f) a b := by
  induction hab with
  | rel x y hxy =>
    obtain ⟨d, hdS, hdU, hdx, hdy⟩ := hxy
    by_cases hd : d = f ∨ d = M.mate f
    · -- the step is the bond `f`: its ends are `j₁, j₂`
      have hends : s(x, y) = s(j₁, j₂) := by
        rcases hd with rfl | rfl
        · rw [← hdx, ← hdy]
          exact hf
        · rw [← hdx, ← hdy, M.mate_mate, ← hf]
          exact Sym2.eq_swap
      rcases Sym2.eq_iff.mp hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hj
      · exact hj.symm
    · push Not at hd
      exact Relation.EqvGen.rel _ _ ⟨d, hd.1, hd.2, hdS, hdU, hdx, hdy⟩
  | refl x => exact Relation.EqvGen.refl x
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂

/-- **The parity step of Lemma P**: the joints of `f` stay joined in `G − f`. -/
theorem joints_conn {γ : ℝ} {M : Molecule V D} {S : Finset V} {j₁ j₂ : V} (hB : M.IsBlock S j₁ j₂) {f : D}
    (hf : M.ends f = s(j₁, j₂)) {n : ℕ} (U : Fin n → Src.Object γ M) (hUS : ∀ i, (U i).atoms ⊆ S)
    (hUj : ∀ i, j₁ ∉ (U i).atoms ∧ j₂ ∉ (U i).atoms)
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i).atoms (U j).atoms) :
    Relation.EqvGen (remAdjWithout M S U f) j₁ j₂ := by
  classical
  by_contra hne
  set R := remAdjWithout M S U f with hR
  have hj₁S : j₁ ∈ S := hB.2.1
  have hj₂S : j₂ ∈ S := hB.2.2.1
  -- the side of `j₁` in `G − f`
  set X : Finset V := S.filter fun w => Relation.EqvGen R j₁ w with hX
  have hj₁X : j₁ ∈ X := mem_filter.mpr ⟨hj₁S, Relation.EqvGen.refl _⟩
  have hj₂X : j₂ ∉ X := fun h => hne (mem_filter.mp h).2
  obtain ⟨f₀, hf₀, hf₀a, hf₀b⟩ := exists_dart_at_j₁ hf
  -- the cut of `S` at `X` is even
  have hSeven : Even (leaving M (M.InGroup S) X).card :=
    even_card_leaving M (M.InGroup S) (inGroup_mate_iff M S) X fun w _ => even_degIn_of_isBlock hB w
  -- the cut of each `E(U°)` at `X` is even
  have hUeven : ∀ i, Even (leaving M (U i).ContainsDart X).card := fun i =>
    even_card_leaving M (U i).ContainsDart (containsDart_mate_iff (U i)) X fun w _ => even_card_containsDart (U i) w
  -- `f` is in no `E(U°)`
  have hfU : ∀ i, ¬ (U i).ContainsDart f₀ := fun i h => by
    have hg := inGroup_of_containsDart (U i) h
    exact (hUj i).1 (hf₀a ▸ hg.1)
  -- the cut of `S` at `X` is `f₀` and the cuts of the `E(U°)`
  have hcut : leaving M (M.InGroup S) X = insert f₀ ((univ : Finset (Fin n)).biUnion fun i =>
      leaving M (U i).ContainsDart X) := by
    ext x
    simp only [mem_insert, mem_biUnion, mem_univ, true_and, mem_leaving]
    constructor
    · rintro ⟨hxS, hxX, hmX⟩
      by_cases hc : ∃ i, (U i).ContainsDart x
      · obtain ⟨i, hi⟩ := hc
        exact Or.inr ⟨i, hi, hxX, hmX⟩
      · push Not at hc
        by_cases hd : x = f ∨ x = M.mate f
        · -- `x` is a dart of `f` at `X`, so it is the dart at `j₁`
          left
          have hxf : x = f₀ ∨ x = M.mate f₀ := by
            rcases hf₀ with rfl | rfl
            · exact hd
            · rw [M.mate_mate]
              exact hd.symm
          rcases hxf with h | h
          · exact h
          · exfalso
            rw [h, hf₀b] at hxX
            exact hj₂X hxX
        · -- otherwise `x` is a bond of `G − f`, which cannot leave `X`
          exfalso
          push Not at hd
          have hstep : R (M.atom x) (M.atom (M.mate x)) := ⟨x, hd.1, hd.2, hxS, hc, rfl, rfl⟩
          have hx1 := (mem_filter.mp hxX).2
          exact hmX (mem_filter.mpr ⟨hxS.2, hx1.trans _ _ _ (Relation.EqvGen.rel _ _ hstep)⟩)
    · rintro (rfl | ⟨i, hi, hxX, hmX⟩)
      · refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
        · rw [hf₀a]
          exact hj₁S
        · rw [hf₀b]
          exact hj₂S
        · rw [hf₀a]
          exact hj₁X
        · rw [hf₀b]
          exact hj₂X
      · have hg := inGroup_of_containsDart (U i) hi
        exact ⟨⟨hUS i hg.1, hUS i hg.2⟩, hxX, hmX⟩
  have hnot : f₀ ∉ (univ : Finset (Fin n)).biUnion fun i => leaving M (U i).ContainsDart X := by
    simp only [mem_biUnion, mem_univ, true_and, mem_leaving, not_exists]
    exact fun i h => hfU i h.1
  have hpd : ((univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint fun i => leaving M (U i).ContainsDart X := by
    intro i _ j _ hij
    rw [Function.onFun, disjoint_left]
    intro x hxi hxj
    have hgi := inGroup_of_containsDart (U i) (mem_leaving.mp hxi).1
    have hgj := inGroup_of_containsDart (U j) (mem_leaving.mp hxj).1
    exact disjoint_left.mp (hdisj i j hij) hgi.1 hgj.1
  rw [hcut, card_insert_of_notMem hnot, card_biUnion hpd] at hSeven
  have hsum : Even (∑ i : Fin n, (leaving M (U i).ContainsDart X).card) :=
    Finset.even_sum _ fun i _ => hUeven i
  exact Nat.not_even_one ((Nat.even_add.mp hSeven).mp hsum)

end LemmaP

/-- **N3 Lemma P (parity)** (`research-gamma-half-3/NOTES.txt` L500–L511). -/
theorem lemmaP : LemmaPStatement.{u, v} := by
  intro V D _ _ _ M γ S j₁ j₂ hV _ f hf n U hUS hUj hdisj hconn a ha b hb
  have hB : M.IsBlock S j₁ j₂ := by
    rcases hV with h | h | h
    · exact h.1
    · exact h.1
    · exact h.1
  exact LemmaP.eqvGen_without_of_joints hf (LemmaP.joints_conn hB hf U hUS hUj hdisj) (hconn a ha b hb)

end WaveTurbulence.TVine.Struct
