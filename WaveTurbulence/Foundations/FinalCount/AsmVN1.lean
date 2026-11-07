/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmDesig
public import WaveTurbulence.Foundations.FinalCount.AsmIntact
public import WaveTurbulence.Foundations.Spine.SourceObjectPairUniqueness
public import WaveTurbulence.Foundations.Spine.SourceHyperDiamondObjects
/-! **FINALCOUNT-ASSEMBLY (VineNodeExists, part 1): the oriented pair of an object at a joint.**  Every object has at each of its two
joints exactly one oriented pair of `ContainsDart` darts (uniqueness: `source_object_joint_pair_unique`; existence here). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem block_joint_pair_exists {S : Finset V} {a b : V} (hB : M.IsBlock S a b) :
    ∃ p q, M.atom p = a ∧ M.atom q = a ∧ M.InGroup S p ∧ M.InGroup S q ∧ M.out p = true ∧ M.out q = false := by
  have h1 : M.outIn S a = 1 := hB.2.2.2.2.1
  have h2 : M.inIn S a = 1 := hB.2.2.2.2.2.1
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp h2
  have hp' : p ∈ (M.dartsAt a).filter fun x => M.InGroup S x ∧ M.out x = true := by
    rw [hp]; exact mem_singleton_self _
  have hq' : q ∈ (M.dartsAt a).filter fun x => M.InGroup S x ∧ M.out x = false := by
    rw [hq]; exact mem_singleton_self _
  simp only [Finset.mem_filter, Molecule.dartsAt, Finset.mem_univ, true_and] at hp' hq'
  exact ⟨p, q, hp'.1, hq'.1, hp'.2.1, hq'.2.1, hp'.2.2, hq'.2.2⟩

theorem object_joint_pair_exists (O : Object M) {v : V} (hv : v = O.upper ∨ v = O.lower) :
    ∃ p q, SourceObjectJointPair O v p q := by
  have key : ∀ (a : V), (a = O.upper ∨ a = O.lower) → (∃ p q, M.atom p = a ∧ M.atom q = a ∧ O.ContainsDart p ∧
      O.ContainsDart q ∧ M.out p = true ∧ M.out q = false) := by
    intro a ha
    rcases O with ⟨S, u, l, sh⟩
    cases sh with
    | vc h =>
      have hB : M.IsBlock S a (if a = u then l else u) := by
        rcases ha with rfl | rfl
        · simpa using h.1
        · by_cases e : a = u
          · subst e; simpa using h.1
          · rw [if_neg e]; exact Mole.block_swap_joints M h.1
      obtain ⟨p, q, hp, hq, hpg, hqg, hpo, hqo⟩ := block_joint_pair_exists hB
      exact ⟨p, q, hp, hq, hpg, hqg, hpo, hqo⟩
    | hyper R =>
      have hB : (Molecule.eraseBond M R.added).IsBlock S a (if a = u then l else u) := by
        rcases ha with rfl | rfl
        · simpa using R.adjoint.1
        · by_cases e : a = u
          · subst e; simpa using R.adjoint.1
          · rw [if_neg e]; exact Mole.block_swap_joints _ R.adjoint.1
      obtain ⟨p, q, hp, hq, hpg, hqg, hpo, hqo⟩ := block_joint_pair_exists hB
      exact ⟨p.1, q.1, hp, hq, ⟨p.2.1, p.2.2, hpg⟩, ⟨q.2.1, q.2.2, hqg⟩, hpo, hqo⟩
  obtain ⟨p, q, h1, h2, h3, h4, h5, h6⟩ := key v hv
  exact ⟨p, q, h1, h2, h3, h4, h5, h6⟩

/-- `ContainsDart` is symmetric under `mate`. -/
theorem containsDart_mate (O : Object M) {z : D} (h : O.ContainsDart z) : O.ContainsDart (M.mate z) := by
  unfold Object.ContainsDart at h ⊢
  rcases hs : O.shape with c | R
  · rw [hs] at h
    exact ⟨by simpa [M.mate_mate] using h.2, by simpa [M.mate_mate] using h.1⟩
  · rw [hs] at h
    obtain ⟨a1, a2, a3⟩ := h
    refine ⟨fun e => a2 (by rw [← M.mate_mate z, e]), fun e => a1 (by
      have := congrArg M.mate e
      rwa [M.mate_mate, M.mate_mate] at this), ⟨by simpa [M.mate_mate] using a3.2, by simpa [M.mate_mate] using a3.1⟩⟩

/-- A dart at an interior atom of an object (all darts of the atom in the group) is a `ContainsDart` dart. -/
theorem containsDart_of_interior (O : Object M) (hdeg : ∀ b ∈ M.atoms, M.deg b ≤ 4)
    (hint : ∀ v ∈ O.atoms, v ≠ O.upper → v ≠ O.lower → M.degIn O.atoms v = 4) {z : D} (hz : M.atom z ∈ O.atoms)
    (h1 : M.atom z ≠ O.upper) (h2 : M.atom z ≠ O.lower) : O.ContainsDart z := by
  have hall : ∀ v ∈ O.atoms, v ≠ O.upper → v ≠ O.lower → ∀ z, M.atom z = v → M.InGroup O.atoms z := by
    intro v hv h1 h2 z hzv
    have hd := hint v hv h1 h2
    have hvm : v ∈ M.atoms := (object_oh O).basic.1 hv
    have hle := hdeg v hvm
    have hsub : (M.dartsAt v).filter (fun x => M.InGroup O.atoms x) ⊆ M.dartsAt v := Finset.filter_subset _ _
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      have : ((M.dartsAt v).filter (fun x => M.InGroup O.atoms x)).card = 4 := hd
      unfold Molecule.deg at hle; omega)
    have hzm : z ∈ M.dartsAt v := by simp [Molecule.dartsAt, hzv]
    have := heq ▸ hzm
    exact (Finset.mem_filter.mp this).2
  have hg := hall _ hz h1 h2 z rfl
  unfold Object.ContainsDart
  rcases hs : O.shape with c | R
  · exact hg
  · have hend : (M.atom R.added = O.upper ∧ M.atom (M.mate R.added) = O.lower) ∨
        (M.atom R.added = O.lower ∧ M.atom (M.mate R.added) = O.upper) := by
      have := R.ends_eq
      unfold Molecule.ends at this
      simpa [Sym2.eq_iff] using this
    refine ⟨?_, ?_, hg⟩
    · intro e
      rw [e] at h1 h2
      rcases hend with ⟨a, b⟩ | ⟨a, b⟩
      · exact h1 a
      · exact h2 a
    · intro e
      rw [e] at h1 h2
      rcases hend with ⟨a, b⟩ | ⟨a, b⟩
      · exact h2 b
      · exact h1 b

end WaveTurbulence.FinalCountAsm
