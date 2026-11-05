/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.BlockFamilyRemoval
public import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic

/-! # Disjoint block deletion preserves every surviving degree modulo two
TARGET `cnblock`: a surviving joint loses exactly two incidences; every
other surviving atom loses none. All counts use actual residual half-edges.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w) (F : Finset (GardenBlockSegment G))

noncomputable instance blockFamilyDartFintype : Fintype (BlockFamilyDart G F) := Fintype.ofFinite _

/-- Old incidences at an atom whose bonds were actually removed. -/
@[expose] noncomputable def removedDartsAt (v : GBranch G.tree) : Finset (GardenDart G) := by
  classical
  exact (G.molecule.dartsAt v).filter (fun x => ∃ B ∈ F, G.molecule.InGroup B.atoms x)

theorem degree_add_removedDartsAt (v : GBranch G.tree) :
    (removeBlockFamily G F).deg v + (removedDartsAt G F v).card = G.molecule.deg v := by
  classical
  have hcard : (removeBlockFamily G F).deg v =
      ((G.molecule.dartsAt v).filter (fun x => ¬ ∃ B ∈ F, G.molecule.InGroup B.atoms x)).card := by
    apply Finset.card_bij (fun x _hx => x.1)
    · intro x hx
      refine mem_filter.mpr ⟨(mem_dartsAt G.molecule v x.1).mpr
        ((mem_dartsAt (removeBlockFamily G F) v x).mp hx),?_⟩
      rintro ⟨B,hB,hi⟩
      exact x.2 B hB hi
    · intro x hx y hy he
      exact Subtype.ext he
    · intro x hx
      obtain ⟨hxv,hn⟩ := mem_filter.mp hx
      have hp : ∀ B ∈ F, ¬ G.molecule.InGroup B.atoms x := fun B hB hi => hn ⟨B,hB,hi⟩
      exact ⟨⟨x,hp⟩,(mem_dartsAt (removeBlockFamily G F) v ⟨x,hp⟩).mpr
        ((mem_dartsAt G.molecule v x).mp hxv),rfl⟩
  rw [hcard]
  have h := (G.molecule.dartsAt v).card_filter_add_card_filter_not
    (fun x => ∃ B ∈ F, G.molecule.InGroup B.atoms x)
  change _ + _ = (G.molecule.dartsAt v).card
  exact (Nat.add_comm _ _).trans h

theorem removedDartsAt_eq_block (hdis : Set.PairwiseDisjoint (F : Set (GardenBlockSegment G)) GardenBlockSegment.atoms)
    (B : GardenBlockSegment G) (hB : B ∈ F) (v : GBranch G.tree) (hv : v ∈ B.atoms) :
    removedDartsAt G F v = (G.molecule.dartsAt v).filter (G.molecule.InGroup B.atoms) := by
  classical
  ext x
  simp only [removedDartsAt,mem_filter]
  constructor
  · rintro ⟨hxv,C,hC,hinside⟩
    have he : C = B := by
      by_contra hn
      have he := (mem_dartsAt G.molecule v x).mp hxv
      exact Finset.disjoint_left.mp (hdis hC hB hn) (he ▸ hinside.1) hv
    exact ⟨hxv,he ▸ hinside⟩
  · rintro ⟨hxv,hi⟩
    exact ⟨hxv,B,hB,hi⟩

theorem removedDartsAt_card_zero_or_two
    (hdis : Set.PairwiseDisjoint (F : Set (GardenBlockSegment G)) GardenBlockSegment.atoms)
    (v : GBranch G.tree) (hv : v ∉ removedBlockInteriors G F) :
    (removedDartsAt G F v).card = 0 ∨ (removedDartsAt G F v).card = 2 := by
  classical
  by_cases hb : ∃ B ∈ F, v ∈ B.atoms
  · obtain ⟨B,hB,hvB⟩ := hb
    right
    rw [removedDartsAt_eq_block G F hdis B hB v hvB]
    have hj : v = B.leftJoint ∨ v = B.rightJoint := by
      by_contra hn
      push Not at hn
      exact hv ((mem_removedBlockInteriors G F v).mpr ⟨B,hB,hvB,hn.1,hn.2⟩)
    have hd := block_joint_degrees G.molecule B.block
    rcases hj with rfl | rfl
    · exact hd.1
    · exact hd.2
  · left
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hxv,B,hB,hi⟩ := mem_filter.mp hx
    have he := (mem_dartsAt _ _ _).mp hxv
    exact hb ⟨B,hB,he ▸ hi.1⟩

/-- Ambient deficit and residual degree have the same parity. -/
theorem block_removal_deficit_modEq
    (hdis : Set.PairwiseDisjoint (F : Set (GardenBlockSegment G)) GardenBlockSegment.atoms)
    (v : GBranch G.tree) (hv : v ∉ removedBlockInteriors G F) :
    Nat.ModEq 2 (4-G.molecule.deg v) ((removeBlockFamily G F).deg v) := by
  have hd := degree_add_removedDartsAt G F v
  have hle := garden_molecule_deg_le_four G v
  rcases removedDartsAt_card_zero_or_two G F hdis v hv with h | h <;>
    dsimp only [Nat.ModEq] <;> omega

end WaveTurbulence.Mole
