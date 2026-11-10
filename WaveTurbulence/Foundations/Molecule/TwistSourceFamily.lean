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

end WaveTurbulence.Twist
