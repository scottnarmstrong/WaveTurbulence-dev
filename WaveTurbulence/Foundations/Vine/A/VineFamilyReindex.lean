/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineFamilyUnique
public import WaveTurbulence.Foundations.Molecule.LFTwist.FamilyState
/-! VINE-A1/A3: reindexing actual family states commutes with both LF choices. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.LFTwist
variable {w : ℕ} {G : Garden w} {ι κ : Type*}

/-- Relabel an actual separated source family. -/
def familyReindex (F : CoreFamily G ι) (e : κ ≃ ι) : CoreFamily G κ where
  kind j := F.kind (e j)
  atoms j := F.atoms (e j)
  upper j := F.upper (e j)
  placement j := F.placement (e j)
  core j := F.core (e j)
  designated j := F.designated (e j)
  separated j k hjk := F.separated (e j) (e k) (e.injective.ne hjk)

/-- Actual next placements commute with reindexing, including the active reverse placement. -/
theorem nextPlacement_reindex (F : CoreFamily G ι) (e : κ ≃ ι) (i j : κ) :
    (familyReindex F e).nextPlacement i j = F.nextPlacement (e i) (e j) := by
  apply CorePlacement.ext_data
  · rw [CoreFamily.nextPlacement_lower, CoreFamily.nextPlacement_lower]
    rfl
  · rw [CoreFamily.nextPlacement_retained, CoreFamily.nextPlacement_retained]
    rfl
  · rw [CoreFamily.nextPlacement_keep, CoreFamily.nextPlacement_keep]
    rfl

/-- The carried family is independent of its enumeration. -/
theorem familyReindex_twist (F : CoreFamily G ι) (e : κ ≃ ι) (i : κ) :
    (familyReindex F e).twist i = familyReindex (F.twist (e i)) e := by
  apply CoreFamily.ext_data
  · rfl
  · rfl
  · rfl
  · exact funext (nextPlacement_reindex F e i)

/-- Relabel only a state's family indices; skeleton, replacements and layered garden are literal. -/
def stateReindex (A : FamilyReconstruction w ι) (e : κ ≃ ι) : FamilyReconstruction w κ where
  skeleton := A.skeleton
  family := familyReindex A.family e
  plain := A.plain
  data := A.data
  layered := A.layered
  decodes := A.decodes

/-- Relabeling also commutes with the false (unchanged skeleton) choice. -/
theorem nextFamily_reindex (A : FamilyReconstruction w ι) (e : κ ≃ ι) (i : κ) (ε : Bool) :
    (stateReindex A e).nextFamily i ε = familyReindex (A.nextFamily (e i) ε) e := by
  cases ε
  · rfl
  · exact familyReindex_twist A.family e i

end WaveTurbulence.VineA
