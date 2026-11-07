/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedDesigCovariance
public import WaveTurbulence.Foundations.Vine.A.VineDesignatedSupport
/-! Whole-support characterization for the R83 successor designation. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA.NormalizedSplice
open Stage1 RedSplice LGSpine.SourceVine
variable {w : ℕ} {G : Garden w}

/-- All unchanged vine-like cases designate the entire group. -/
theorem isDesig_atoms_of_vineLikeGroup {S : Finset (GBranch G.tree)} {a : GBranch G.tree}
    {O : Object G.molecule} (h : IsDesig G S a O) (hVL : VineLikeGroup G S) : O.atoms = S := by
  rcases hs : (groupUnitsOf G S).skip with _ | sk
  · by_cases hu : (groupUnitsOf G S).units = []
    · exact h.2.2.2.2.2.2.1 hs hu hVL
    · exact (h.2.2.2.2.1 hs hu).1
  · rcases hb : sk.bond with _ | e
    · exact (h.2.2.1 sk hs hb).1
    · exact (h.2.2.2.1 sk e hs hb).1

theorem designatedObject_atoms {S : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroups G.molecule) (hVL : VineLikeGroup G S) :
    ∃ O, designatedObject G S = some O ∧ O.atoms = S := by
  obtain ⟨a, O, _, hO, hd⟩ := designatedObject_spec hS
  exact ⟨O, hO, isDesig_atoms_of_vineLikeGroup hd hVL⟩

theorem designatedObject_ordinary {S : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroups G.molecule) {a b : GBranch G.tree} (hVC : IsVC G.molecule S a b) :
    ∃ O, designatedObject G S = some O ∧ O.atoms = S ∧ objectHyperTag O = false := by
  obtain ⟨O, hO, ha⟩ := designatedObject_atoms hS ⟨a, b, Or.inr (Or.inl hVC)⟩
  exact ⟨O, hO, ha, object_tag_of_block O (ha.symm ▸ hVC.1)⟩

end WaveTurbulence.VineA.NormalizedSplice
