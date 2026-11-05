/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeConcatenationRealization
public import WaveTurbulence.Foundations.Molecule.MoleculeComponentPartitions
import Mathlib.Tactic

/-!
# Connected block and hyper-block realizations

TARGET `defblock` and DH23 Definition 4.10, with the explicit connected
adjoint convention documented by MoleculeBlockEdgeCase. Hyper-blocks retain
the actual added bond, so multiple joint bonds are handled without quotient
or representative ambiguity.
-/

public section
namespace WaveTurbulence.Mole
open Finset
universe u v
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- An actual block, or an actual hyper-block with its connected adjoint. -/
inductive BlockRealization (S : Finset V) (a b : V) : Type (max u v)
  | block (isBlock : M.IsBlock S a b) (connected : GroupConnected M S)
  | hyper (bond : D) (ends : M.ends bond = s(a,b))
      (isBlock : (eraseBond M bond).IsBlock S a b)
      (connected : GroupConnected (eraseBond M bond) S)

namespace BlockRealization
variable {M}

/-- Actual internal degree of either joint. -/
@[expose] def jointDegree {S : Finset V} {a b : V} : BlockRealization M S a b → ℕ
  | .block _ _ => 2
  | .hyper _ _ _ _ => 3

theorem jointDegree_cases {S : Finset V} {a b : V} (R : BlockRealization M S a b) :
    R.jointDegree = 2 ∨ R.jointDegree = 3 := by cases R <;> simp [jointDegree]

theorem atoms_subset {S : Finset V} {a b : V} (R : BlockRealization M S a b) : S ⊆ M.atoms := by
  cases R with
  | block hB hc => exact hB.1
  | hyper e he hB hc => exact hB.1

theorem joints_mem_ne {S : Finset V} {a b : V} (R : BlockRealization M S a b) :
    a ∈ S ∧ b ∈ S ∧ a ≠ b := by
  cases R with
  | block hB hc => exact ⟨hB.2.1,hB.2.2.1,hB.2.2.2.1⟩
  | hyper e he hB hc => exact ⟨hB.2.1,hB.2.2.1,hB.2.2.2.1⟩

/-- The actual degree profile, proved from the realization rather than
included as an unproved input to the overlap theorem. -/
theorem degrees {S : Finset V} {a b : V} (R : BlockRealization M S a b) :
    M.degIn S a = R.jointDegree ∧ M.degIn S b = R.jointDegree ∧
      ∀ v ∈ S, v ≠ a → v ≠ b → M.degIn S v = 4 := by
  cases R with
  | block hB hc => exact ⟨(block_joint_degrees M hB).1,(block_joint_degrees M hB).2,hB.2.2.2.2.2.2.2.2.1⟩
  | hyper e he hB hc => exact hyperBlock_degrees M ⟨e,he,hB⟩

end BlockRealization

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
/-- Deleting a whole bond only removes induced paths, never adds one. -/
theorem eraseBond_induced_path (e : D) (S : Finset V) {u v : V}
    (hp : (induced (eraseBond M e) S).SameComponent u v) : (induced M S).SameComponent u v := by
  induction hp with
  | rel a b hab =>
    obtain ⟨⟨x,hx,hb⟩,haS,hbS⟩ := (induced_adj_iff (eraseBond M e) S a b).mp hab
    exact Relation.EqvGen.rel _ _ ((induced_adj_iff M S a b).mpr ⟨⟨x.1,hx,hb⟩,haS,hbS⟩)
  | refl => exact Relation.EqvGen.refl _
  | symm a b hab ih => exact sameComponent_symm (induced M S) ih
  | trans a b c hab hbc ihab ihbc => exact sameComponent_trans (induced M S) ihab ihbc

variable {M}

/-- Connectedness of a realized hyper-block follows from its connected
adjoint by the actual inclusion of the old half-edges. -/
theorem BlockRealization.connected {S : Finset V} {a b : V} (R : BlockRealization M S a b) :
    GroupConnected M S := by
  cases R with
  | block hB hc => exact hc
  | hyper e he hB hc => exact ⟨hc.1,fun u hu v hv => eraseBond_induced_path M e S (hc.2 u hu v hv)⟩

/-- No realized joint carries a loop, including in a hyper-block: its
added bond joins distinct joints and every old loop would survive deletion. -/
theorem BlockRealization.no_joint_loop {S : Finset V} {a b : V} (R : BlockRealization M S a b)
    (x : D) (hx : M.atom x = a ∨ M.atom x = b) : M.atom (M.mate x) ≠ M.atom x := by
  cases R with
  | block hB hc => exact connected_block_no_joint_loop M hB hc hx
  | hyper e he hB hc =>
    intro hloop
    have hne := hB.2.2.2.1
    have hend : (M.atom e = a ∧ M.atom (M.mate e) = b) ∨
        (M.atom e = b ∧ M.atom (M.mate e) = a) := Sym2.eq_iff.mp he
    have hends : M.atom e ≠ M.atom (M.mate e) := by
      rcases hend with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · rw [h1,h2]
        exact hne
      · rw [h1,h2]
        exact Ne.symm hne
    have hx1 : x ≠ e := by
      intro hh
      subst x
      exact hends hloop.symm
    have hx2 : x ≠ M.mate e := by
      intro hh
      subst x
      rw [M.mate_mate] at hloop
      exact hends hloop
    let y : {x : D // x ≠ e ∧ x ≠ M.mate e} := ⟨x,hx1,hx2⟩
    have hn := connected_block_no_joint_loop (eraseBond M e) hB hc (x := y) hx
    exact hn hloop

/-- A realized block/hyper-block with any interior atom uses strictly
fewer joint-to-joint bonds than its full joint degree. -/
theorem BlockRealization.sigma_lt_jointDegree {S : Finset V} {a b : V}
    (R : BlockRealization M S a b) (hproper : S ≠ {a,b}) : M.sigma a b < R.jointDegree := by
  cases R with
  | block hB hc =>
    have hle := block_sigma_le_two M hB
    have hn : M.sigma a b ≠ 2 := fun hs => hproper (connected_block_eq_pair_of_sigma_two M hB hc hs)
    change M.sigma a b < 2
    omega
  | hyper e he hB hc =>
    let R : BlockRealization M S a b := .hyper e he hB hc
    have hne := hB.2.2.2.1
    have hnoa : ∀ x, M.atom x = a → M.atom (M.mate x) ≠ a := by
      intro x hx
      have hh := R.no_joint_loop x (Or.inl hx)
      rw [hx] at hh
      exact hh
    have hnoE : ∀ x, (eraseBond M e).atom x = a → (eraseBond M e).atom ((eraseBond M e).mate x) ≠ a := by
      intro x hx
      have hh := connected_block_no_joint_loop (eraseBond M e) hB hc (Or.inl hx)
      rw [hx] at hh
      exact hh
    have hd := (eraseBond_joint_degrees M e he hne (by simp) (by simp) (S := {a,b})).1
    rw [degIn_pair_eq_bondsBetween M hne hnoa,
      degIn_pair_eq_bondsBetween (eraseBond M e) hne hnoE] at hd
    have hle := block_sigma_le_two (eraseBond M e) hB
    have hn : (eraseBond M e).sigma a b ≠ 2 :=
      fun hs => hproper (connected_block_eq_pair_of_sigma_two (eraseBond M e) hB hc hs)
    change (eraseBond M e).bondsBetween a b ≤ 2 at hle
    change (eraseBond M e).bondsBetween a b ≠ 2 at hn
    change M.bondsBetween a b < 3
    omega

end WaveTurbulence.Mole
