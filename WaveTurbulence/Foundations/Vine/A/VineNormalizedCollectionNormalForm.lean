/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineContributingTransport
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedCollectionSupport
/-! A choice-free normal form for the actual collection's list of atom supports. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset Stage1 RedSplice LGSpine.SourceVine
open scoped Classical
variable {w : ℕ} {G : Garden w}

/-- Exactly the SG maximal groups which actually contribute a C1 object. -/
noncomputable def contributingGroups (G : Garden w) (σ : Prescription G) : List (Finset (GBranch G.tree)) := by
  classical
  exact (sgGroups G σ).filter (fun S => decide (HasObj G S))

/-- The actual chosen object's support is fixed whenever the group contributes. -/
theorem objOf_atoms (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG) :
    (objOf G σ S).map Object.atoms =
      if HasObj G S then some (S.image ((stSt G σ).M.pi (stSt G σ).hcls)) else none := by
  classical
  by_cases ho : HasObj G S
  · have hh : G.molecule.IsMolecule ∧ S ∈ maximalGroups G.molecule ∧ σ S = Molecule.GapKind.SG ∧ HasObj G S :=
      ⟨Mole.garden_isMolecule G, hS, hσ, ho⟩
    rw [ite_eq_left ho]
    unfold objOf
    rw [dite_eq_left ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2, not_markedGroup_empty G S, exists_obj hh.1 σ hS hσ ho⟩]
    exact congrArg some (objSpec_atoms σ hS hσ (Classical.choose_spec (exists_obj hh.1 σ hS hσ ho)))
  · have hh : ¬ (G.molecule.IsMolecule ∧ S ∈ maximalGroups G.molecule ∧ σ S = Molecule.GapKind.SG ∧ HasObj G S) :=
      fun h => ho h.2.2.2
    rw [ite_eq_right ho]
    unfold objOf
    rw [dite_eq_right (fun h' => hh ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1⟩)]
    rfl

/-- The full support list of actual collection choices is independent of the object witnesses. -/
theorem objects_atoms_eq (σ : Prescription G) :
    (objects G σ).map Object.atoms =
      (contributingGroups G σ).map (fun S => S.image ((stSt G σ).M.pi (stSt G σ).hcls)) := by
  classical
  unfold objects contributingGroups
  rw [List.map_filterMap]
  have he : (sgGroups G σ).filterMap (fun S => (objOf G σ S).map Object.atoms) =
      (sgGroups G σ).filterMap (fun S => if HasObj G S then some (S.image ((stSt G σ).M.pi (stSt G σ).hcls)) else none) := by
    apply List.filterMap_congr
    intro S hS
    exact objOf_atoms σ (mem_sgGroups.mp hS).1 (mem_sgGroups.mp hS).2
  rw [he]
  induction sgGroups G σ with
  | nil => rfl
  | cons S L ih =>
    by_cases hs : HasObj G S <;> simp [hs, ih]

end WaveTurbulence.VineA.NormalizedSplice
