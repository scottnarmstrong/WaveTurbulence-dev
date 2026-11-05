/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistFamilyCounting

/-! # Source-facing twists of a q-member collection of CL vines

TARGET Definition twist (L1429): only the core members are acted on.
The common-joint condition implies the weaker separation assumed here.
Every concrete placement is produced from the source vine statements.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- Source data for a q-member collection of CL vines. The source additionally
restricts a possible shared atom to a joint; at most one common atom suffices here. -/
structure SourceVineFamily {w : ℕ} (G : Garden w) (q : ℕ) where
  kind : Fin q → VineType
  atoms : Fin q → Finset (GBranch G.tree)
  upper : Fin q → GBranch G.tree
  lower : Fin q → GBranch G.tree
  vine : ∀ i, G.molecule.IsVine (kind i) (atoms i) (upper i) (lower i)
  cl : ∀ i, Mole.CLParentPattern G (atoms i) (upper i) (lower i)
  separated : ∀ i j, i ≠ j → SeparatedGroups (atoms i) (atoms j)

variable {w q : ℕ} {G : Garden w}

/-- Exactly the eligible core members of the given source collection. -/
abbrev SourceVineFamily.CoreIndex (F : SourceVineFamily G q) :=
  {i : Fin q // IsCoreCLVine G (F.kind i) (F.atoms i) (F.upper i) (F.lower i)}

noncomputable instance (F : SourceVineFamily G q) : Fintype F.CoreIndex := Fintype.ofFinite _

/-- The designated concrete source placement, derived rather than assumed. -/
@[expose] noncomputable def SourceVineFamily.corePlacement (F : SourceVineFamily G q) (i : F.CoreIndex) :
    CorePlacement G := Classical.choose (corePlacement_at_vine G i.2)

/-- The chosen concrete placement has the exact internal slot of the input vine. -/
theorem SourceVineFamily.corePlacement_at (F : SourceVineFamily G q) (i : F.CoreIndex) :
    IsPlacementAt G (F.atoms i) (F.lower i) (F.corePlacement i) :=
  Classical.choose_spec (corePlacement_at_vine G i.2)

/-- The source collection produces a core family with all placement conditions proved. -/
@[expose] noncomputable def SourceVineFamily.coreFamily (F : SourceVineFamily G q) : CoreFamily G F.CoreIndex where
  kind i := F.kind i
  atoms i := F.atoms i
  upper i := F.upper i
  placement := F.corePlacement
  core i := (F.corePlacement_at i).1.symm ▸ i.2
  designated i := (F.corePlacement_at i).1.symm ▸ F.corePlacement_at i
  separated i j hij := F.separated i j (fun he => hij (Subtype.ext he))

/-- The literal source garden collection, obtained by choosing a subset of core vines. -/
@[expose] noncomputable def SourceVineFamily.twists (F : SourceVineFamily G q) : Set (Garden w) :=
  familyTwists ⟨G,F.coreFamily⟩

/-- A source twist collection is finite. -/
theorem SourceVineFamily.twists_finite (F : SourceVineFamily G q) : F.twists.Finite :=
  familyTwists_finite ⟨G,F.coreFamily⟩

/-- Exact source twist count: one independent binary choice for each core member. -/
theorem SourceVineFamily.twists_ncard (F : SourceVineFamily G q) :
    F.twists.ncard = 2 ^ Fintype.card F.CoreIndex := familyTwists_ncard ⟨G,F.coreFamily⟩

/-- There are at most q core members in the original q-member collection. -/
theorem SourceVineFamily.core_count_le (F : SourceVineFamily G q) : Fintype.card F.CoreIndex ≤ q := by
  exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin q)

/-- TARGET Definition twist: the number of actual gardens is a power of two
and at most 2^q, including empty collections and collections without core vines. -/
theorem SourceVineFamily.twists_count (F : SourceVineFamily G q) :
    (∃ r ≤ q, F.twists.ncard = 2 ^ r) ∧ F.twists.ncard ≤ 2 ^ q := by
  refine ⟨⟨Fintype.card F.CoreIndex,F.core_count_le,F.twists_ncard⟩,?_⟩
  exact F.twists_ncard.le.trans (Nat.pow_le_pow_right (by decide) F.core_count_le)

end WaveTurbulence.Twist
