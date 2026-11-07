/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.TreeFacts
public import WaveTurbulence.Foundations.Molecule.GardenIncidence
import Mathlib.Tactic

/-! # Atoms of degree four in a garden molecule (TARGET defcplmol, L1297–L1302)

An atom of degree `4` is a non-root branching node all of whose three children carry a dart: a branching child
(a PC dart) or a leaf child with unmarked partner having a parent (an LP dart).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open TTree
variable {w : ℕ}

theorem deg4_position (G : Garden w) (x : GBranch G.tree) (hx : G.molecule.deg x = 4) (pos : Fin 4) :
    ∃ d : GardenDart G, G.molecule.atom d = x ∧ Mole.dartPosition G d = pos := by
  have hinj : Set.InjOn (Mole.dartPosition G) (G.molecule.dartsAt x : Set (GardenDart G)) := by
    intro d hd e he hde
    apply Mole.atom_position_injective G
    apply Prod.ext
    · exact ((Mole.mem_dartsAt G.molecule x d).mp hd).trans
        ((Mole.mem_dartsAt G.molecule x e).mp he).symm
    · exact hde
  have hc : ((G.molecule.dartsAt x).image (Mole.dartPosition G)).card = 4 := by
    rw [Finset.card_image_of_injOn hinj]; exact hx
  have hu : (G.molecule.dartsAt x).image (Mole.dartPosition G) = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa using hc)
  have : pos ∈ (G.molecule.dartsAt x).image (Mole.dartPosition G) := by rw [hu]; exact Finset.mem_univ _
  obtain ⟨d, hd, hdp⟩ := Finset.mem_image.mp this
  exact ⟨d, (Mole.mem_dartsAt G.molecule x d).mp hd, hdp⟩

theorem deg4_nonroot (G : Garden w) (x : GBranch G.tree) (hx : G.molecule.deg x = 4) : x.1.2 ≠ [] := by
  intro h
  have := Mole.root_degree_le_three G x h
  omega

/-- Every child of an atom of degree four is a branching node, or a leaf with an LP dart. -/
theorem deg4_child (G : Garden w) (x : GBranch G.tree) (hx : G.molecule.deg x = 4) (i : Fin 3) :
    (∃ c : GBranch G.tree, c.toNode = x.child i) ∨
      ∃ ℓ : GLeaf G.tree, ℓ.toNode = x.child i ∧ G.mark ℓ = none ∧ (G.pair ℓ).1.2 ≠ [] := by
  obtain ⟨d, hda, hdp⟩ := deg4_position G x hx i.succ
  rcases d with ⟨c, _ | _⟩ | ℓ
  · have h0 : (0 : Fin 4) = i.succ := hdp
    exact absurd h0.symm (Fin.succ_ne_zero i)
  · left
    refine ⟨c.1, ?_⟩
    have hp : GNode.parent c.1.toNode c.2 = x := hda
    have hl : c.1.1.2.getLast c.2 = i := by
      have : (c.1.1.2.getLast c.2).succ = i.succ := hdp
      exact Fin.succ_inj.mp this
    rw [← Mole.parent_child_eq_node c.1.toNode c.2, hp]
    exact congrArg x.child hl
  · right
    refine ⟨ℓ.1, ?_, ℓ.2.1, ℓ.2.2.2⟩
    have hp : GNode.parent ℓ.1.toNode ℓ.2.2.1 = x := hda
    have hl : ℓ.1.1.2.getLast ℓ.2.2.1 = i := by
      have : (ℓ.1.1.2.getLast ℓ.2.2.1).succ = i.succ := hdp
      exact Fin.succ_inj.mp this
    rw [← Mole.parent_child_eq_node ℓ.1.toNode ℓ.2.2.1, hp]
    exact congrArg x.child hl

end WaveTurbulence.LayerCnt
