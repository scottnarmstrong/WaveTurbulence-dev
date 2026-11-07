/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.S1Basic
public import WaveTurbulence.Foundations.Molecule.MoleculeHyperBlocks
public import WaveTurbulence.Foundations.Molecule.MoleculeOrientationGroups
public import WaveTurbulence.Foundations.Molecule.VineErasedGroupBonds
public import WaveTurbulence.Foundations.Molecule.MoleculeConcatenationRealization
public import WaveTurbulence.Foundations.Molecule.MoleculeJointSymmetry
public import WaveTurbulence.Foundations.Spine.SourceChainSwap
public import WaveTurbulence.Foundations.Spine.SourceJointPairDichotomy
import Mathlib.Tactic

/-!
# Stage 1 combinatorics: deleting a bond outside a group, and unions at one joint

Deleting a bond that is not internal to an atomic group `S` does not change `S` as a block, a vine
or a vine chain.  This transports ordinary chains into the adjoint molecule, and gives the union
of two chains meeting in one joint as a designated vine-like object (a VC, or an HVC when the outer
joints are joined by a bond).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Stage1
open Finset WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem inGroup_mate' {S : Finset V} {x : D} (h : M.InGroup S x) : M.InGroup S (M.mate x) :=
  ⟨h.2, by rw [M.mate_mate]; exact h.1⟩

theorem ne_of_inGroup {S : Finset V} {e x : D} (he : ¬ M.InGroup S e) (hx : M.InGroup S x) :
    x ≠ e ∧ x ≠ M.mate e := by
  refine ⟨fun h => he (h ▸ hx), fun h => he ?_⟩
  have := inGroup_mate' hx
  rw [h, M.mate_mate] at this
  exact this

theorem isBlock_eraseBond {S : Finset V} {a b : V} (e : D) (hB : M.IsBlock S a b)
    (he : ¬ M.InGroup S e) : (Molecule.eraseBond M e).IsBlock S a b := by
  obtain ⟨hS, ha, hb, hne, ho1, hi1, ho2, hi2, hint, hconn⟩ := hB
  have hdeg : ∀ v, (Molecule.eraseBond M e).degIn S v = M.degIn S v := by
    intro v
    have h1 : (Molecule.eraseBond M e).degIn S v =
        (((M.dartsAt v).filter (M.InGroup S)) \ {e, M.mate e}).card :=
      Mole.eraseBond_degIn M e S v
    rw [h1]
    unfold Molecule.degIn
    congr 1
    apply Finset.sdiff_eq_self_iff_disjoint.mpr
    rw [Finset.disjoint_right]
    intro x hx hxv
    have hxg := (Finset.mem_filter.mp hxv).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact he hxg
    · exact he (by simpa only [M.mate_mate] using inGroup_mate' hxg)
  have hori : ∀ v (c : Bool), (((Molecule.eraseBond M e).dartsAt v).filter
      (fun x => (Molecule.eraseBond M e).InGroup S x ∧ (Molecule.eraseBond M e).out x = c)).card =
      ((M.dartsAt v).filter (fun x => M.InGroup S x ∧ M.out x = c)).card :=
    fun v c => Mole.eraseBond_orientedIn M e S v c he
  refine ⟨hS, ha, hb, hne, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hori a true).trans ho1
  · exact (hori a false).trans (by
      have := hi1
      unfold Molecule.inIn at this
      simpa using this)
  · exact (hori b true).trans ho2
  · exact (hori b false).trans (by
      have := hi2
      unfold Molecule.inIn at this
      simpa using this)
  · intro v hv h1 h2
    exact (hdeg v).trans (hint v hv h1 h2)
  · intro u hu v hv
    refine Relation.EqvGen.mono ?_ u v (hconn u hu v hv)
    rintro p q ⟨x, hx, hxp, hxq⟩
    obtain ⟨h1, h2⟩ := ne_of_inGroup he hx
    exact ⟨⟨x, h1, h2⟩, hx, hxp, hxq⟩

theorem eraseBond_groupBonds_eq {S : Finset V} (e : D) (he : ¬ M.InGroup S e) :
    (Molecule.eraseBond M e).groupBonds S = M.groupBonds S := by
  have h := Vine.eraseBond_groupBonds_filter M e S
  change (Mole.eraseBond M e).groupBonds S = _ at h
  change (Mole.eraseBond M e).groupBonds S = _
  rw [h]
  unfold Molecule.groupBonds
  congr 1
  rw [Finset.filter_true_of_mem]
  intro d hd
  have hdg := (Finset.mem_filter.mp hd).2.2
  exact ne_of_inGroup he hdg

theorem isVine_eraseBond {X : VineType} {S : Finset V} {a b : V} (e : D)
    (hV : M.IsVine X S a b) (he : ¬ M.InGroup S e) : (Molecule.eraseBond M e).IsVine X S a b := by
  obtain ⟨hB, k, hk, f, hf, hi, hj, hg⟩ := hV
  exact ⟨isBlock_eraseBond e hB he, k, hk, f, hf, hi, hj, by rw [eraseBond_groupBonds_eq e he]; exact hg⟩

theorem inGroup_mono {S T : Finset V} (h : S ⊆ T) {x : D} (hx : M.InGroup S x) : M.InGroup T x :=
  ⟨h hx.1, h hx.2⟩

theorem chain_eraseBond {S : Finset V} {a b : V} {n : ℕ} (e : D) (h : Chain M S a b n)
    (he : ¬ M.InGroup S e) : Chain (Molecule.eraseBond M e) S a b n := by
  induction h with
  | single hv =>
    obtain ⟨X, hX⟩ := hv
    exact Chain.single ⟨X, isVine_eraseBond e hX he⟩
  | @append S' T a b c n hS hT hi hne ih =>
    obtain ⟨X, hX⟩ := hT
    refine Chain.append (ih (fun h' => he (inGroup_mono subset_union_left h'))) ⟨X, isVine_eraseBond e hX
      (fun h' => he (inGroup_mono subset_union_right h'))⟩ hi hne

/-- A chain `P` from `a` to `c` and a chain `Q` from `c` to `b` meeting exactly in `c`, both
ordinary blocks: the union is a designated vine-like object (a VC, or an HVC if the outer joints
are joined by a further bond). -/
theorem exists_object_union (hM : M.IsMolecule) {P Q : Finset V} {a b c : V} {n m : ℕ}
    (hP : Chain M P a c n) (hQ : Chain M Q c b m) (hPQ : P ∩ Q = {c})
    (hPB : M.IsBlock P a c) (hQB : M.IsBlock Q c b) :
    ∃ W : Object M, W.atoms = P ∪ Q ∧ W.upper = a ∧ W.lower = b := by
  have hcon := Mole.blocks_concatenate M hM hPB (Mole.block_swap_joints M hQB) (groupConnected_of_block hPB) hPQ
  rcases hcon with hU | ⟨e, he, hBe⟩
  · exact ⟨⟨P ∪ Q, a, b, .vc ⟨hU, n + m, chain_append_chain hP hQ hPQ⟩⟩, rfl, rfl, rfl⟩
  · have hbP : b ∉ P := by
      intro hb
      have : b ∈ P ∩ Q := mem_inter.mpr ⟨hb, (chain_ends hQ).2.1⟩
      rw [hPQ] at this
      exact (chain_ends hQ).2.2 (mem_singleton.mp this).symm
    have haQ : a ∉ Q := by
      intro ha
      have : a ∈ P ∩ Q := mem_inter.mpr ⟨(chain_ends hP).1, ha⟩
      rw [hPQ] at this
      exact (chain_ends hP).2.2 (mem_singleton.mp this)
    have hend := Sym2.eq_iff.mp he
    change (M.atom e = a ∧ M.atom (M.mate e) = b) ∨ (M.atom e = b ∧ M.atom (M.mate e) = a) at hend
    have hnP : ¬ M.InGroup P e := by
      rintro ⟨h1, h2⟩
      rcases hend with ⟨_, h4⟩ | ⟨h3, _⟩
      · exact hbP (h4 ▸ h2)
      · exact hbP (h3 ▸ h1)
    have hnQ : ¬ M.InGroup Q e := by
      rintro ⟨h1, h2⟩
      rcases hend with ⟨h3, _⟩ | ⟨_, h4⟩
      · exact haQ (h3 ▸ h1)
      · exact haQ (h4 ▸ h2)
    have hP' := chain_eraseBond e hP hnP
    have hQ' := chain_eraseBond e hQ hnQ
    exact ⟨⟨P ∪ Q, a, b, .hyper ⟨e, he, ⟨hBe, n + m, chain_append_chain hP' hQ' hPQ⟩⟩⟩, rfl, rfl, rfl⟩

end WaveTurbulence.Stage1
