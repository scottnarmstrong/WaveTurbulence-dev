/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LeafPairPositions

/-! # Exhausting three ordered child slots by actual incidences

TARGET molecpl: the three distinct child incidences exhaust the children.
-/

public section
namespace WaveTurbulence.Molecpl
open TTree
variable {w : ℕ} (G : Garden w)

/-- Three distinct LP incidences at an atom force all its children to be leaves. -/
theorem three_LP_children {v : GBranch G.tree} (D : Fin 3 → GardenDart G)
    (hinj : Function.Injective D) (ha : ∀ t, G.molecule.atom (D t) = v)
    (hlp : ∀ t, ¬ IsPCDart G (D t)) :
    ∀ i : Fin 3, ∃ l : GLeaf G.tree, l.toNode = v.child i := by
  have hw (t : Fin 3) := dart_leaf_pair_positions G (hlp t) (ha t) rfl
  choose l p q _hm hl _hr hpos _hq using hw
  have hp : Function.Injective p := by
    intro i j he
    have hd : Mole.dartPosition G (D i) = Mole.dartPosition G (D j) := by
      rw [hpos i,hpos j,he]
    exact hinj (Mole.atom_position_injective G (Prod.ext ((ha i).trans (ha j).symm) hd))
  have hs := Finite.surjective_of_injective hp
  intro i
  obtain ⟨t,ht⟩ := hs i
  exact ⟨l t,by simpa only [ht] using hl t⟩

/-- Three distinct non-parent incidence positions exhaust the child slots. -/
theorem three_child_positions {v : GBranch G.tree} (D : Fin 3 → GardenDart G)
    (hinj : Function.Injective D) (ha : ∀ t, G.molecule.atom (D t) = v)
    (p : Fin 3 → Fin 3) (hpos : ∀ t, Mole.dartPosition G (D t) = (p t).succ) :
    Function.Surjective p := by
  apply Finite.surjective_of_injective
  intro i j he
  have hd : Mole.dartPosition G (D i) = Mole.dartPosition G (D j) := by
    rw [hpos i,hpos j,he]
  exact hinj (Mole.atom_position_injective G (Prod.ext ((ha i).trans (ha j).symm) hd))

end WaveTurbulence.Molecpl
