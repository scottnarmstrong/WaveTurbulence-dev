/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Spine.VineDelObjects` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.Spine.VineDelMolecule
public import WaveTurbulence.Foundations.Molecule.VineTwoJointSeparator
public import WaveTurbulence.Foundations.Molecule.VineHyperBothJoints
public import WaveTurbulence.Foundations.Molecule.VineLikeConnected
public import WaveTurbulence.Foundations.Molecule.MoleculeComponentPartitions
public import WaveTurbulence.Foundations.Molecule.MoleculeBlockRealizations
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
/-! # The interior deletion property for actual vine chains and designated vine-like objects -/
public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.Vine Finset WaveTurbulence.GammaLow.FinalCount

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]


/-- DH23 Lemma 4.11 premise for vine chains: deleting an interior atom leaves the chain connected
or splits it into two connected pieces containing the joints. -/
theorem chain_interior_deletion {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain γ M S a b n) {v : V} (hv : v ∈ S) (hva : v ≠ a) (hvb : v ≠ b) :
    Mole.GroupConnected M (S.erase v) ∨ Mole.TwoComponents M (S.erase v) a b := by
  classical
  obtain ⟨haS, hbS⟩ := chain_joints_mem h
  have haS' : a ∈ S.erase v := mem_erase.mpr ⟨hva.symm, haS⟩
  have hbS' : b ∈ S.erase v := mem_erase.mpr ⟨hvb.symm, hbS⟩
  have reach := chain_erase_endpoint_reach (z := v) h
  by_cases hab : (Mole.induced M (S.erase v)).SameComponent a b
  · left
    have hall : ∀ u ∈ S.erase v, (Mole.induced M (S.erase v)).SameComponent a u := by
      intro u hu
      rcases reach u hu with ⟨_, hp⟩ | ⟨_, hp⟩
      · exact hp
      · exact Relation.EqvGen.trans _ _ _ hab hp
    refine ⟨⟨a, haS'⟩, fun u hu w hw => ?_⟩
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hall u hu)) (hall w hw)
  · right
    let U := (S.erase v).filter (fun x => (Mole.induced M (S.erase v)).SameComponent a x)
    let W := (S.erase v).filter (fun x => (Mole.induced M (S.erase v)).SameComponent b x)
    have hclosed : ∀ (c : V), (Mole.induced M (S.erase v)).SameComponent c c →
        ∀ x ∈ (S.erase v).filter (fun x => (Mole.induced M (S.erase v)).SameComponent c x),
        ∀ y ∈ S.erase v, M.Adj x y →
        y ∈ (S.erase v).filter (fun x => (Mole.induced M (S.erase v)).SameComponent c x) := by
      intro c _ x hx y hy hadj
      refine mem_filter.mpr ⟨hy, Relation.EqvGen.trans _ _ _ (mem_filter.mp hx).2
        (Relation.EqvGen.rel _ _ ((Mole.induced_adj_iff M _ x y).mpr ⟨hadj, (mem_filter.mp hx).1, hy⟩))⟩
    have gc : ∀ (c : V), c ∈ S.erase v →
        Mole.GroupConnected M ((S.erase v).filter
          (fun x => (Mole.induced M (S.erase v)).SameComponent c x)) := by
      intro c hc
      refine ⟨⟨c, mem_filter.mpr ⟨hc, Relation.EqvGen.refl _⟩⟩, fun u hu w hw => ?_⟩
      have hcl := hclosed c (Relation.EqvGen.refl _)
      have hp : (Mole.induced M (S.erase v)).SameComponent u w :=
        Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (mem_filter.mp hu).2)
          (mem_filter.mp hw).2
      exact (induced_restrict M hcl hp).2 hu
    refine ⟨U, W, ?_, ?_, gc a haS', gc b hbS',
      mem_filter.mpr ⟨haS', Relation.EqvGen.refl _⟩,
      mem_filter.mpr ⟨hbS', Relation.EqvGen.refl _⟩, ?_⟩
    · ext u
      simp only [mem_union, U, W, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hu
        rcases reach u hu with ⟨_, hp⟩ | ⟨_, hp⟩
        · exact Or.inl ⟨hu, hp⟩
        · exact Or.inr ⟨hu, hp⟩
    · rw [Finset.disjoint_left]
      intro u hu hw
      exact hab (Relation.EqvGen.trans _ _ _ (mem_filter.mp hu).2
        (Relation.EqvGen.symm _ _ (mem_filter.mp hw).2))
    · intro u hu w hw hadj
      have hp := Relation.EqvGen.rel _ _ ((Mole.induced_adj_iff M (S.erase v) u w).mpr
        ⟨hadj, (mem_filter.mp hu).1, (mem_filter.mp hw).1⟩)
      exact hab (Relation.EqvGen.trans _ _ _ (mem_filter.mp hu).2
        (Relation.EqvGen.trans _ _ _ hp (Relation.EqvGen.symm _ _ (mem_filter.mp hw).2)))

section Objects

theorem sourceVC_chain {M : Molecule V D} {S : Finset V} {a b : V}
    (h : Src.IsVC γ M S a b) : ∃ n, Src.Chain γ M S a b n := by
  obtain ⟨_, n, hc⟩ := h
  exact ⟨n, hc⟩

/-- Interior deletion property for an ordinary designated VC. -/
theorem sourceVC_interior_deletion {M : Molecule V D} {S : Finset V} {a b : V}
    (h : Src.IsVC γ M S a b) : Mole.InteriorDeletionProperty M S a b := by
  obtain ⟨n, hc⟩ := sourceVC_chain h
  intro v hv hva hvb
  exact chain_interior_deletion hc hv hva hvb

/-- Interior deletion property of a hyper-like object, in the original molecule. -/
theorem hyperAdjoint_interior_deletion {M : Molecule V D} {S : Finset V} {a b : V} {e : D}
    (hends : M.ends e = s(a, b)) (h : Src.IsVC γ (Mole.eraseBond M e) S a b) :
    Mole.InteriorDeletionProperty M S a b := by
  obtain ⟨n, hc⟩ := sourceVC_chain h
  intro v hv hva hvb
  have hadj : M.Adj a b := by
    have h2 : s(M.atom e, M.atom (M.mate e)) = s(a, b) := hends
    rcases Sym2.eq_iff.mp h2 with ⟨h1, h3⟩ | ⟨h1, h3⟩
    · exact ⟨e, h1, h3⟩
    · exact ⟨M.mate e, h3, by rw [M.mate_mate]; exact h1⟩
  have tr : ∀ {U : Finset V}, Mole.GroupConnected (Mole.eraseBond M e) U → Mole.GroupConnected M U :=
    fun {U} hU => ⟨hU.1, fun u hu w hw => eraseBond_induced_path M e U (hU.2 u hu w hw)⟩
  rcases chain_interior_deletion hc hv hva hvb with hcn | ⟨U, W, hUW, _, hU, hW, haU, hbW, _⟩
  · exact Or.inl (tr hcn)
  · left
    have hUS : U ⊆ S.erase v := hUW ▸ subset_union_left
    have hWS : W ⊆ S.erase v := hUW ▸ subset_union_right
    have hU' := tr hU
    have hW' := tr hW
    refine ⟨⟨a, hUS haU⟩, fun u hu w hw => ?_⟩
    have all : ∀ x ∈ S.erase v, (Mole.induced M (S.erase v)).SameComponent a x := by
      intro x hx
      have hx' : x ∈ U ∪ W := hUW ▸ hx
      rcases mem_union.mp hx' with hxU | hxW
      · exact induced_path_mono M hUS (hU'.2 a haU x hxU)
      · refine Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _
          ((Mole.induced_adj_iff M (S.erase v) a b).mpr ⟨hadj, hUS haU, hWS hbW⟩))
          (induced_path_mono M hWS (hW'.2 b hbW x hxW))
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (all u hu)) (all w hw)

/-- All premises of the overlap classification (DH23 Lemma 4.11) hold for every actual
designated vine-like object. -/
theorem object_overlap_premises {M : Molecule V D} (O : Src.Object γ M) :
    Nonempty (Mole.BlockRealization M O.atoms O.upper O.lower) ∧
    Mole.InteriorDeletionProperty M O.atoms O.upper O.lower ∧
    (∀ x ∈ O.atoms \ {O.upper, O.lower}, ∀ y ∈ O.atoms \ {O.upper, O.lower},
      (Mole.induced M (O.atoms \ {O.upper, O.lower})).SameComponent x y) := by
  rcases O with ⟨S, a, b, shape⟩
  cases shape with
  | vc h =>
    obtain ⟨n, hc⟩ := sourceVC_chain h
    refine ⟨⟨Mole.BlockRealization.block h.1 ⟨⟨a, (chain_joints_mem hc).1⟩,
      chain_connected hc⟩⟩, sourceVC_interior_deletion h, chain_interior_connected hc⟩
  | hyper R =>
    obtain ⟨n, hc⟩ := sourceVC_chain R.adjoint
    refine ⟨⟨Mole.BlockRealization.hyper R.added R.ends_eq R.adjoint.1
      ⟨⟨a, (chain_joints_mem hc).1⟩, chain_connected hc⟩⟩,
      hyperAdjoint_interior_deletion R.ends_eq R.adjoint, ?_⟩
    intro x hx y hy
    exact eraseBond_induced_path M R.added _ (chain_interior_connected hc x hx y hy)

end Objects

end WaveTurbulence.GammaLow.Fama
