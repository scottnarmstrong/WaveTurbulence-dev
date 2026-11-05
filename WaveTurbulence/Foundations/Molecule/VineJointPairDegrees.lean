/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRestrictInsertion
public import WaveTurbulence.Foundations.Molecule.VineSigmaExpansion
public import WaveTurbulence.Foundations.Molecule.VineRealizationDegrees
import Mathlib.Tactic

/-! # Exact degrees in the two-joint atomic subgroup -/

public section
namespace WaveTurbulence.Vine
open Finset

/-- All literal bonds between joint labels are retained exactly under expansion. -/
theorem expand_restrict_joints (X : VineType) (k : List ℕ)
    (hk : k.length=X.template.slots.length) :
    restrictBonds {0,1} (X.expand k).bonds=restrictBonds {0,1} X.template.bonds := by
  have hslots : slotMembers (X.template.slots.zip k)=
      X.template.slots.flatMap (fun s => [s.1,s.2]) := by
    conv_rhs => rw [← List.map_fst_zip (l₂ := k) hk.symm.le]
    rw [List.flatMap_map]
    rfl
  have hr := template_slots_ready X
  have hn : 2 ≤ X.template.n := by cases X <;> decide
  have hh := fold_insertRungs_invariant
    (fun T => 2 ≤ T.n ∧ restrictBonds {0,1} T.bonds=restrictBonds {0,1} X.template.bonds)
    (fun s => 2 ≤ s.1.1 ∧ 2 ≤ s.2.1)
    (fun T s k hs hT _hm1 _hm2 => by
      have he := restrict_insertRungs_external ({0,1} : Finset ℕ) T s k
        (by intro hh; simp only [mem_insert,mem_singleton] at hh; omega)
        (by intro hh; simp only [mem_insert,mem_singleton] at hh; omega)
        (by intro i _hi; simp only [mem_insert,mem_singleton]; omega)
        (by intro i _hi; simp only [mem_insert,mem_singleton]; omega)
      exact ⟨by rw [insertRungs_atoms]; omega,he.trans hT.2⟩)
    (X.template.slots.zip k) X.template ⟨hn,rfl⟩
    (fun sk hsk => template_slots_interior X sk.1 (List.of_mem_zip hsk).1)
    (hslots ▸ hr.1) (hslots ▸ hr.2)
  exact hh.2

/-- Finite base-table calculation of either joint's induced pair degree. -/
theorem template_joint_pair_degree (X : VineType) (v : ℕ) (hv : v=0 ∨ v=1) :
    edgeDegree (restrictBonds {0,1} X.template.bonds) v=
      templateSigma X.template := by
  cases X <;> rcases hv with rfl | rfl <;> rfl

variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- TARGET defvine: the actual two-joint subgroup has degree two for I,
one for V and zero for all other vines, independently of inserted ladders. -/
theorem isVine_joint_pair_degrees {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (hV : M.IsVine X S a b) :
    M.degIn {a,b} a=(templateSigma X.template) ∧
      M.degIn {a,b} b=(templateSigma X.template) := by
  obtain ⟨hB,⟨R⟩⟩ := isVine_iff_realization.mp hV
  have hsub : ({a,b} : Finset V) ⊆ S := by
    intro v hv
    rcases mem_insert.mp hv with hv | hv
    · exact hv ▸ hB.2.1
    · exact mem_singleton.mp hv ▸ hB.2.2.1
  have himage : ({a,b} : Finset V).image R.f=({0,1} : Finset ℕ) := by
    simp only [image_insert,image_singleton]
    exact R.joints_eq
  have hd (v : V) (hv : v=a ∨ v=b) :
      M.degIn {a,b} v=(templateSigma X.template) := by
    have hvS : v ∈ S := hv.elim (fun h => h.symm ▸ hB.2.1) (fun h => h.symm ▸ hB.2.2.1)
    have hh := R.subgroup_degree hsub hvS
    rw [himage] at hh
    change M.degIn {a,b} v=edgeDegree (restrictBonds {0,1} (X.expand R.k).bonds) (R.f v) at hh
    rw [expand_restrict_joints X R.k R.length_eq] at hh
    have hvm : R.f v ∈ ({0,1} : Finset ℕ) := by
      rw [← R.joints_eq]
      simpa only [mem_insert,mem_singleton] using hv.elim
        (fun h => Or.inl (congrArg R.f h)) (fun h => Or.inr (congrArg R.f h))
    exact hh.trans (template_joint_pair_degree X (R.f v) (by simpa only [mem_insert,mem_singleton] using hvm))
  exact ⟨hd a (Or.inl rfl),hd b (Or.inr rfl)⟩

end WaveTurbulence.Vine
