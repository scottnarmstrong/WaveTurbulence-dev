/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistSpecialParents

/-! # Exact values of the exceptional PC/LP transposition -/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The lower PC incidences become the two retained LP incidences. -/
theorem exceptionalDartSwap_lowerPC (side : Bool) :
    exceptionalDartSwap G P (lowerPC G P side) =
      if side then G.molecule.mate (retainedLP G P) else retainedLP G P := by
  have hp := Garden.pair_ne_of_unmarked P.unmarked
  cases side <;> simp [exceptionalDartSwap,Equiv.trans_apply,Equiv.swap_apply_def,
    lowerPC,retainedLP,Garden.molecule,hp.symm]

/-- The retained LP incidence becomes the lower child-end PC incidence. -/
theorem exceptionalDartSwap_retainedLP :
    exceptionalDartSwap G P (retainedLP G P) = lowerPC G P false := by
  simp [exceptionalDartSwap,Equiv.trans_apply,Equiv.swap_apply_def,
    lowerPC,retainedLP,Garden.molecule]

/-- The paired LP incidence becomes the parent-end PC incidence. -/
theorem exceptionalDartSwap_pairedLP :
    exceptionalDartSwap G P (G.molecule.mate (retainedLP G P)) = lowerPC G P true := by
  have hp := Garden.pair_ne_of_unmarked P.unmarked
  simp [exceptionalDartSwap,Equiv.trans_apply,Equiv.swap_apply_def,
    lowerPC,retainedLP,Garden.molecule,hp]

/-- Every other actual PC incidence is fixed by the exceptional transposition. -/
theorem exceptionalDartSwap_otherPC (c : {c : GBranch G.tree // c.1.2 ≠ []})
    (hc : c.1 ≠ P.lower) (side : Bool) :
    exceptionalDartSwap G P (.inl (c,side)) = (.inl (c,side) : GardenDart G) := by
  have hcb : c ≠ ⟨P.lower,P.nonroot⟩ := fun he => hc (congrArg Subtype.val he)
  simp [exceptionalDartSwap,Equiv.trans_apply,Equiv.swap_apply_def,
    lowerPC,retainedLP,Garden.molecule,hcb]

/-- Every other actual LP incidence is fixed by the exceptional transposition. -/
theorem exceptionalDartSwap_otherLP
    (l : {l : GLeaf G.tree // G.mark l = none ∧ l.1.2 ≠ [] ∧ (G.pair l).1.2 ≠ []})
    (hl : l.1 ≠ P.retained) (hp : l.1 ≠ G.pair P.retained) :
    exceptionalDartSwap G P (.inr l) = (.inr l : GardenDart G) := by
  simp [exceptionalDartSwap,Equiv.trans_apply,Equiv.swap_apply_def,
    lowerPC,retainedLP,Garden.molecule,Subtype.ext_iff,hl,hp]

end WaveTurbulence.Twist
