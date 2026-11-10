/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineHVGroupKey
public import WaveTurbulence.Foundations.Vine.A.VineDVGroupKey
/-! Exact success and validity specifications consumed by the R83 successors. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Mole WaveTurbulence.LGSpine.SourceVine
variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)}

/-- The single-HV selector always returns one valid triple in its approved case. -/
theorem hvGroupPick_some (hS : SingleHVGroup G S) :
    ∃ a b e, hvGroupPick G S = some (a, b, e) ∧ G.molecule.ends e = s(a, b) ∧
      Vine.IsSomeVine (eraseBond G.molecule e) S a b := by
  classical
  let t := (hvGroupKey_existsUnique hS).choose
  refine ⟨t.1.1, t.1.2.1, t.1.2.2, ?_, t.2⟩
  unfold hvGroupPick
  rw [dite_eq_left hS]

/-- The pure-DV selector always returns one valid whole constituent triple. -/
theorem dvGroupPick_some (hS : PureDVGroup G S) :
    ∃ A a b, dvGroupPick G S = some (A, a, b) ∧ DVCandidate G S (A, a, b) := by
  classical
  let t := (dvGroupKey_existsUnique hS).choose
  refine ⟨t.1.1, t.1.2.1, t.1.2.2, ?_, t.2⟩
  unfold dvGroupPick
  rw [dite_eq_left hS]

/-- A returned HV triple satisfies the original deleted-bond realization predicate. -/
theorem hvGroupPick_valid {a b : GBranch G.tree} {e : GardenDart G}
    (h : hvGroupPick G S = some (a, b, e)) :
    G.molecule.ends e = s(a, b) ∧ Vine.IsSomeVine (eraseBond G.molecule e) S a b :=
  (hvGroupPick_spec h).choose_spec.choose

/-- A returned DV triple supplies both original type-V constituent realizations. -/
theorem dvGroupPick_valid {A : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (h : dvGroupPick G S = some (A, a, b)) :
    ∃ B, G.molecule.IsVine .V A a b ∧ G.molecule.IsVine .V B a b ∧ A ∩ B = {a, b} ∧ S = A ∪ B :=
  (dvGroupPick_spec h).2.1

end WaveTurbulence.VineA
