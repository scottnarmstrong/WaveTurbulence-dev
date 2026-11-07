/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.FinalCount.RedSpliceColl
public import Mathlib.Logic.Equiv.Set
/-! Group names after the actual all-SG splice. The names distinguish every
original maximal group and retain the entire local prescription carrier.
This file does not assert ordered LF invariance of the normalizing garden. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset Stage1 RedSplice Represents
variable {w : ℕ} {G : Garden w}

/-- Splicing never identifies atoms from distinct maximal groups. -/
theorem spliced_group_images_disjoint (σ : Prescription G)
    {S T : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule)
    (hT : T ∈ maximalGroups G.molecule) (hne : S ≠ T) :
    Disjoint (S.image ((stSt G σ).M.pi (stSt G σ).hcls))
      (T.image ((stSt G σ).M.pi (stSt G σ).hcls)) := by
  classical
  rw [Finset.disjoint_left]
  intro c hc hd
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hd
  have hr : repC (stSt G σ).cls y = repC (stSt G σ).cls x :=
    ((stSt G σ).M.ob_pi (stSt G σ).hcls y).symm.trans
      ((congrArg (stSt G σ).M.ob he).trans ((stSt G σ).M.ob_pi (stSt G σ).hcls x))
  exact Finset.disjoint_left.mp (groups_disjoint (Mole.garden_isMolecule G) hS hT hne)
    (repC_mem_group (Mole.garden_isMolecule G) σ hS hx)
    (hr ▸ repC_mem_group (Mole.garden_isMolecule G) σ hT hy)

/-- Even a wholly contracted group has a nonempty, distinct quotient support. -/
theorem spliced_group_image_injective (σ : Prescription G) :
    Function.Injective (fun S : {S // S ∈ maximalGroups G.molecule} =>
      S.1.image ((stSt G σ).M.pi (stSt G σ).hcls)) := by
  classical
  intro S T he
  apply Subtype.ext
  by_contra hn
  obtain ⟨x, hx⟩ := S.2.1.nonempty
  have hc := Finset.mem_image_of_mem ((stSt G σ).M.pi (stSt G σ).hcls) hx
  change S.1.image _ = T.1.image _ at he
  have hd := hc
  rw [he] at hd
  exact Finset.disjoint_left.mp (spliced_group_images_disjoint σ S.2 T.2 hn) hc hd

/-- A normalization using all of V, independent of the eventual prescription. -/
noncomputable def coarseSplice (G : Garden w) : SpState G := stSt G (fun _ => .SG)

/-- A group's name is its whole image support, not a maximal group of the quotient. -/
noncomputable def coarseGroupCode (G : Garden w)
    (S : {S // S ∈ maximalGroups G.molecule}) : Finset (GBranch (coarseSplice G).G.tree) := by
  classical
  exact S.1.image ((coarseSplice G).M.pi (coarseSplice G).hcls)

/-- No two original maximal groups have the same normalized name. -/
theorem coarseGroupCode_injective (G : Garden w) : Function.Injective (coarseGroupCode G) :=
  spliced_group_image_injective (fun _ => .SG)

/-- The normalized names carry exactly the original maximal-group index type. -/
noncomputable def coarseGroupCodeEquiv (G : Garden w) :
    {S // S ∈ maximalGroups G.molecule} ≃ Set.range (coarseGroupCode G) :=
  Equiv.ofInjective (coarseGroupCode G) (coarseGroupCode_injective G)

/-- Reindexing by normalized names retains every local coloring, including
colorings which distinguish different groups in one hypothetical loop orbit. -/
noncomputable def coarsePrescriptionEquiv (G : Garden w) :
    GroupPrescription G ≃ (Set.range (coarseGroupCode G) → Molecule.GapKind) :=
  Equiv.arrowCongr (coarseGroupCodeEquiv G) (Equiv.refl _)

/-- The original color is recovered at the code of every original group. -/
theorem coarsePrescriptionEquiv_apply (σ : GroupPrescription G)
    (S : {S // S ∈ maximalGroups G.molecule}) :
    coarsePrescriptionEquiv G σ (coarseGroupCodeEquiv G S) = σ S :=
  congrArg σ ((coarseGroupCodeEquiv G).symm_apply_apply S)

end WaveTurbulence.VineA
