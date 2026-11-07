/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineCollectionSupport
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSpliceHingePair
/-! Full quotient supports of the successor collection choices. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset Stage1 RedSplice LGSpine.SourceVine
variable {w : ℕ} {G : Garden w}

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

end WaveTurbulence.VineA.NormalizedSplice
