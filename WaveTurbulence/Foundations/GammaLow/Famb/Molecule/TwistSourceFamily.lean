/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistSourceFamily
-- L5b port of `WaveTurbulence.Foundations.Molecule.TwistSourceFamily` (see COPIED-SHA256SUMS): the source family of
-- a chain over 𝒱_γ; main's field `vine` (every member a drawn vine) is dropped, the rest is verbatim.

/-! # Source-facing twists of a q-member collection over `𝒱_γ`

TARGET Definition twist (L1429): only the core members are acted on. A core member is a CL vine (I) or (II)
(`IsCoreCLVine`), the same in both families (note 3 §4.3: the bad vines of `𝒱_γ` are (I), (II)), so the twist data of
main apply verbatim; a member of `𝒱_γ` that is not a drawn vine (a T-vine) is never core. Accordingly main's field
`vine : ∀ i, IsVine (kind i) …` is not part of this structure: `kind` is a label, read only through `IsCoreCLVine`.
-/

public section
namespace WaveTurbulence.GammaLow.Famb.Twist
open WaveTurbulence.Twist TTree

/-- Source data for a q-member collection of CL vines of `𝒱_γ` (main's `SourceVineFamily` without `vine`). -/
structure SourceVineFamilyΓ {w : ℕ} (G : Garden w) (q : ℕ) where
  kind : Fin q → VineType
  atoms : Fin q → Finset (GBranch G.tree)
  upper : Fin q → GBranch G.tree
  lower : Fin q → GBranch G.tree
  cl : ∀ i, Mole.CLParentPattern G (atoms i) (upper i) (lower i)
  separated : ∀ i j, i ≠ j → SeparatedGroups (atoms i) (atoms j)

variable {w q : ℕ} {G : Garden w}

/-- Exactly the eligible core members of the given source collection. -/
abbrev SourceVineFamilyΓ.CoreIndex (F : SourceVineFamilyΓ G q) :=
  {i : Fin q // IsCoreCLVine G (F.kind i) (F.atoms i) (F.upper i) (F.lower i)}

noncomputable instance (F : SourceVineFamilyΓ G q) : Fintype F.CoreIndex := Fintype.ofFinite _

/-- The designated concrete source placement, derived rather than assumed. -/
@[expose] noncomputable def SourceVineFamilyΓ.corePlacement (F : SourceVineFamilyΓ G q) (i : F.CoreIndex) :
    CorePlacement G := Classical.choose (corePlacement_at_vine G i.2)

/-- The chosen concrete placement has the exact internal slot of the input vine. -/
theorem SourceVineFamilyΓ.corePlacement_at (F : SourceVineFamilyΓ G q) (i : F.CoreIndex) :
    IsPlacementAt G (F.atoms i) (F.lower i) (F.corePlacement i) :=
  Classical.choose_spec (corePlacement_at_vine G i.2)

/-- The source collection produces a core family with all placement conditions proved. -/
@[expose] noncomputable def SourceVineFamilyΓ.coreFamily (F : SourceVineFamilyΓ G q) : CoreFamily G F.CoreIndex where
  kind i := F.kind i
  atoms i := F.atoms i
  upper i := F.upper i
  placement := F.corePlacement
  core i := (F.corePlacement_at i).1.symm ▸ i.2
  designated i := (F.corePlacement_at i).1.symm ▸ F.corePlacement_at i
  separated i j hij := F.separated i j (fun he => hij (Subtype.ext he))

end WaveTurbulence.GammaLow.Famb.Twist
