/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePrescribedFieldIso
public import WaveTurbulence.Foundations.FinalCount.RedSpliceColl2
/-! Actual chosen collection objects have the full quotient support of their
original maximal group, independently of the skipped-vine presentation. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset Stage1 RedSplice LGSpine.SourceVine
variable {w : ℕ} {G : Garden w}

/-- Collapsing the two runs leaves exactly the image of the skipped ingredient. -/
theorem skipped_group_image (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG)
    (sk : SkipData G S) (hsk : (groupUnitsOf G S).skip = some sk) :
    S.image ((stSt G σ).M.pi (stSt G σ).hcls) =
      sk.A.image ((stSt G σ).M.pi (stSt G σ).hcls) := by
  classical
  let M := (stSt G σ).M
  let π := M.pi (stSt G σ).hcls
  have hxA : sk.x ∈ sk.A := sk.vine.choose_spec.1.2.1
  have hyA : sk.y ∈ sk.A := sk.vine.choose_spec.1.2.2.1
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
    rw [sk.hS] at hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · have hL : sk.L0 ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨z, hz⟩
        obtain ⟨u, hu, hua⟩ := unit_L (Mole.garden_isMolecule G) σ hS hσ hsk hL
        have hxL : sk.x ∈ sk.L0 := (sk.left.resolve_left (fun h => hL h.1)).2.2.1
        have he : π z = π sk.x := by
          apply M.ob_inj
          rw [M.ob_pi, M.ob_pi,
            stSt_repC_mem (Mole.garden_isMolecule G) σ hu (hua ▸ hz),
            stSt_repC_mem (Mole.garden_isMolecule G) σ hu (hua ▸ hxL)]
        exact Finset.mem_image.mpr ⟨sk.x, hxA, he.symm⟩
      · exact Finset.mem_image_of_mem π hz
    · have hR : sk.R0 ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨z, hz⟩
      obtain ⟨u, hu, hua⟩ := unit_R (Mole.garden_isMolecule G) σ hS hσ hsk hR
      have hyR : sk.y ∈ sk.R0 := (sk.right.resolve_left (fun h => hR h.1)).2.2.1
      have he : π z = π sk.y := by
        apply M.ob_inj
        rw [M.ob_pi, M.ob_pi,
          stSt_repC_mem (Mole.garden_isMolecule G) σ hu (hua ▸ hz),
          stSt_repC_mem (Mole.garden_isMolecule G) σ hu (hua ▸ hyR)]
      exact Finset.mem_image.mpr ⟨sk.y, hyA, he.symm⟩
  · apply Finset.image_subset_image
    intro z hz
    have hh : z ∈ sk.L0 ∪ sk.A ∪ sk.R0 := Finset.mem_union_left _ (Finset.mem_union_right _ hz)
    exact sk.hS.symm ▸ hh

/-- Every actual chosen collection support is the entire image of its original group. -/
theorem objSpec_atoms (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG)
    {O : Object (stSt G σ).G.molecule} (hO : ObjSpec G σ S O) :
    O.atoms = S.image ((stSt G σ).M.pi (stSt G σ).hcls) := by
  obtain ⟨A, hAS, ha, hcover, hcase⟩ := hO.src
  rcases hcase with ⟨hHV, _, _⟩ | ⟨sk, hsk, rfl, _⟩
  · have he : A = S := Finset.Subset.antisymm hAS (fun z hz => hcover z hz
      (stSt_cls_none (Mole.garden_isMolecule G) σ
        (fun u hu => no_unit_hv (Mole.garden_isMolecule G) σ hS hHV.1 hHV.2 hz u hu)))
    exact ha.trans (congrArg (Finset.image ((stSt G σ).M.pi (stSt G σ).hcls)) he)
  · exact ha.trans (skipped_group_image σ hS hσ sk hsk).symm

/-- The actual constructed list of collection objects has no arbitrary support choice. -/
theorem mem_objects_atoms (σ : Prescription G) {O : Object (stSt G σ).G.molecule}
    (hO : O ∈ objects G σ) :
    ∃ S ∈ maximalGroups G.molecule, σ S = Molecule.GapKind.SG ∧
      O.atoms = S.image ((stSt G σ).M.pi (stSt G σ).hcls) := by
  obtain ⟨S, _, hS, hσ, hs⟩ := mem_objects hO
  exact ⟨S, hS, hσ, objSpec_atoms σ hS hσ hs⟩

end WaveTurbulence.VineA
