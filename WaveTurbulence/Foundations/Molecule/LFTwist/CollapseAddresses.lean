/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.StretchOrder
public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.ReplaceTree

/-! # Matching the exact C3 collapse embedding to the C4 outside move -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Links
variable {w : ℕ}

theorem under_iff_below_addr (a z : Address w) : Under a z ↔ Below a z :=
  and_congr eq_comm Iff.rfl

/-- C3 prefix insertion is exactly C4 relocation from the upper to the lone root. -/
theorem stretch_eq_shift (a z : Address w) (p : Path) :
    stretch a p z = shiftAddr a (addrExt a p) z := by
  by_cases hz : Below a z
  · have hu := (under_iff_below_addr a z).mpr hz
    change z.1 = a.1 ∧ a.2 <+: z.2 at hz
    rw [stretch, ite_eq_left hz, shiftAddr, ite_eq_left hu]
    exact Prod.ext hz.1 rfl
  · rw [stretch_outside a p z hz, shift_of_not
      (fun ht => hz ((under_iff_below_addr a z).mp ht))]

/-- On exactly the surviving source region, the two address maps are inverses. -/
theorem stretch_shift_collapse (a z : Address w) (p : Path)
    (hz : ¬ InTree a (addrExt a p) z) :
    stretch a p (shiftAddr (addrExt a p) a z) = z := by
  rw [stretch_eq_shift]
  exact shift_shift ⟨rfl,List.prefix_refl _⟩ hz

/-- The collapsed garden has no removed paired-tree interval. -/
theorem not_inTree_self (a z : Address w) : ¬ InTree a a z := fun h => h.2 h.1

/-- The collapse move is a left inverse on every new address. -/
theorem shift_stretch_collapse (a z : Address w) (p : Path) :
    shiftAddr (addrExt a p) a (stretch a p z) = z := by
  rw [stretch_eq_shift]
  exact shift_shift (under_ext a p) (not_inTree_self a z)

/-- Every new address is sent outside the removed source interval. -/
theorem stretch_outside_tree_interval (a z : Address w) (p : Path) :
    ¬ InTree a (addrExt a p) (stretch a p z) := by
  rw [stretch_eq_shift]
  exact out_shift (not_inTree_self a z)

end WaveTurbulence.LFTwist
