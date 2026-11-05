/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineJointBonds
import Mathlib.Tactic

/-! # Sigma of every expanded vine template (TARGET defvine) -/

public section
namespace WaveTurbulence.Vine

/-- All dashed insertion slots lie away from the joints. -/
theorem template_slots_interior (X : VineType) :
    ∀ s ∈ X.template.slots, 2 ≤ s.1.1 ∧ 2 ≤ s.2.1 := by
  cases X <;> decide

/-- The complete expansion retains exactly the base joint bonds. -/
theorem expand_sigma_eq (X : VineType) (k : List ℕ)
    (hk : k.length=X.template.slots.length) : templateSigma (X.expand k)=templateSigma X.template := by
  have hslots : slotMembers (X.template.slots.zip k) =
      X.template.slots.flatMap (fun s => [s.1,s.2]) := by
    conv_rhs => rw [← List.map_fst_zip (l₂ := k) hk.symm.le]
    rw [List.flatMap_map]
    rfl
  have hr := template_slots_ready X
  have hh := fold_insertRungs_invariant
    (fun T => 2 ≤ T.n ∧ templateSigma T=templateSigma X.template)
    (fun s => 2 ≤ s.1.1 ∧ 2 ≤ s.2.1)
    (fun T s k hs hT h1 h2 => ⟨by rw [insertRungs_atoms]; omega,
      (insertRungs_sigma T s k hT.1 h1 h2 hs.1 hs.2).trans hT.2⟩)
    (X.template.slots.zip k) X.template
    ⟨by cases X <;> decide,rfl⟩
    (fun sk hsk => template_slots_interior X sk.1 (List.of_mem_zip hsk).1)
    (hslots ▸ hr.1) (hslots ▸ hr.2)
  exact hh.2

/-- TARGET defvine: sigma is two for I, one for V, and zero otherwise,
independently of all inserted ladders. -/
theorem expand_sigma (X : VineType) (k : List ℕ)
    (hk : k.length=X.template.slots.length) :
    templateSigma (X.expand k) = match X with | .I => 2 | .V => 1 | _ => 0 := by
  rw [expand_sigma_eq X k hk,template_sigma]
  cases X <;> rfl

end WaveTurbulence.Vine
