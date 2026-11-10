/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineFamily
public import WaveTurbulence.Foundations.Molecule.TwistFamilyExtensionality
/-! VINE-A1: duplicate-free enumeration and uniqueness up to reindexing of the
specified core vine carrier. Every statement concerns actual CoreFamily data. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.Stage1 WaveTurbulence.Twist
variable {w : ℕ} {G : Garden w}

/-- The geometric CL vine represented by a family member. -/
def familyVine {ι : Type*} (F : CoreFamily G ι) (i : ι) : CLVine G where
  atoms := F.atoms i
  upper := F.upper i
  lower := (F.placement i).lower
  isVine := ⟨F.kind i, (F.core i).1⟩
  notParentUpper := (F.core i).2.1.1
  parentLower := (F.core i).2.1.2

/-- A separated core family cannot enumerate one atom set twice. -/
theorem family_atoms_injective {ι : Type*} (F : CoreFamily G ι) : Function.Injective F.atoms := by
  intro i j h
  by_contra hne
  have hu : F.upper i ∈ F.atoms i := (F.core i).1.1.2.1
  have hl : (F.placement i).lower ∈ F.atoms i := (F.core i).1.1.2.2.1
  have he := F.separated i j hne (F.upper i) hu (h ▸ hu) (F.placement i).lower hl (h ▸ hl)
  exact (F.core i).1.1.2.2.2.1 he

/-- The lower joint and designated internal child determine a core placement. -/
theorem placement_unique {S : Finset (GBranch G.tree)} {b : GBranch G.tree}
    {P Q : CorePlacement G} (hP : IsPlacementAt G S b P) (hQ : IsPlacementAt G S b Q) : P = Q := by
  have hl : P.lower = Q.lower := hP.1.trans hQ.1.symm
  have hk : P.keep = Q.keep := (hQ.2 P.keep).mp ((hP.2 P.keep).mpr rfl)
  apply CorePlacement.ext_data hl _ hk
  apply Subtype.ext
  change P.retained.toNode.1 = Q.retained.toNode.1
  rw [P.child, Q.child, hl, hk]

/-- Map any exact enumeration to the canonical subtype of the intended carrier. -/
noncomputable def indexEquiv {ι : Type*} (F : CoreFamily G ι) (U : Set (CLVine G))
    (hmem : ∀ i, familyVine F i ∈ U)
    (hcover : ∀ c ∈ U, (∃ X, IsCoreCLVine G X c.atoms c.upper c.lower) →
      ∃ i, F.atoms i = c.atoms) : ι ≃ CoreIndex U := by
  let f : ι → CoreIndex U := fun i => ⟨familyVine F i, hmem i, F.kind i, F.core i⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    apply family_atoms_injective F
    exact congrArg (fun x : CoreIndex U => x.1.atoms) hij
  · intro c
    obtain ⟨i, hi⟩ := hcover c.1 c.2.1 c.2.2
    exact ⟨i, Subtype.ext (clVine_eq_of_atoms hi)⟩

/-- Consequently the chosen actual placements agree under the reindexing. -/
theorem indexEquiv_placement {ι : Type*} (F : CoreFamily G ι) (U : Set (CLVine G))
    (hmem : ∀ i, familyVine F i ∈ U)
    (hcover : ∀ c ∈ U, (∃ X, IsCoreCLVine G X c.atoms c.upper c.lower) →
      ∃ i, F.atoms i = c.atoms) (i : ι) :
    corePlacementOf U (indexEquiv F U hmem hcover i) = F.placement i := by
  apply placement_unique (corePlacementOf_spec U _)
  exact F.designated i

end WaveTurbulence.VineA
