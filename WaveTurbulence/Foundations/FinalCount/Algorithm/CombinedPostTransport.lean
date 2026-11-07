/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.DartRelabelingNormalizedCount
public import WaveTurbulence.Foundations.FinalCount.AppBCombinedRemoval
public import WaveTurbulence.Foundations.FinalCount.AppBConditionedDeletion
import Mathlib.Tactic

/-! # Flattened combined-removal counts give the actual successive post count -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
variable {M : Molecule V D} {P Q : AppbPattern}

noncomputable def combinedPostDartEquiv (r : AppbRealization M P) (s : AppbRealization r.post Q)
    (v0 : M.atoms) : Degen.RetainedDart M (r.combinedRemoval s v0).removedAtoms ≃
      Degen.RetainedDart r.post s.removedAtoms := by
  have he : (r.combinedRemoval s v0).removedAtoms = r.removedAtoms ∪ s.removedAtoms :=
    r.combinedRemoval_removed s v0
  have hf (x : Degen.RetainedDart M (r.combinedRemoval s v0).removedAtoms) :
      (M.atom x.val ∉ r.removedAtoms ∧ M.atom x.val ∉ s.removedAtoms) ∧
      (M.atom (M.mate x.val) ∉ r.removedAtoms ∧ M.atom (M.mate x.val) ∉ s.removedAtoms) := by
    let z : D := x.val
    have h1 : M.atom z ∉ (r.combinedRemoval s v0).removedAtoms := x.property.1
    have h2 : M.atom (M.mate z) ∉ (r.combinedRemoval s v0).removedAtoms := x.property.2
    rw [he] at h1 h2
    exact ⟨notMem_union.mp h1,notMem_union.mp h2⟩
  have hg (x : Degen.RetainedDart r.post s.removedAtoms) :
      M.atom x.val.val ∉ (r.combinedRemoval s v0).removedAtoms ∧
      M.atom (M.mate x.val.val) ∉ (r.combinedRemoval s v0).removedAtoms := by
    rw [he]
    exact ⟨notMem_union.mpr ⟨x.val.property.1,x.property.1⟩,
      notMem_union.mpr ⟨x.val.property.2,x.property.2⟩⟩
  exact {
    toFun := fun x => ⟨⟨x.val,(hf x).1.1,(hf x).2.1⟩,(hf x).1.2,(hf x).2.2⟩
    invFun := fun x => ⟨x.val.val,(hg x).1,(hg x).2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem combinedPost_atoms_eq (r : AppbRealization M P) (s : AppbRealization r.post Q) (v0 : M.atoms) :
    (r.combinedRemoval s v0).post.atoms = s.post.atoms := by
  change M.atoms \ (r.combinedRemoval s v0).removedAtoms = (M.atoms \ r.removedAtoms) \ s.removedAtoms
  rw [r.combinedRemoval_removed s v0]
  ext a
  simp only [AppbRealization.combinedRemovedAtoms,mem_sdiff,mem_union]
  tauto

/-- Exact pullback of the flattened source post predicate. It keeps every
old requirement and the same fixed combined local-label tuple. -/
def combinedSequentialAdmissibility (r : AppbRealization M P) (s : AppbRealization r.post Q)
    (v0 : M.atoms) {d : ℕ} (A : (D → (Fin d → ℤ)) → Prop)
    (q : Fin (r.combinedPattern s).edges.length → (Fin d → ℤ))
    (ζ : Degen.RetainedDart r.post s.removedAtoms → (Fin d → ℤ)) : Prop :=
  (r.combinedRemoval s v0).conditionedPostAdmissibility A q (ζ ∘ combinedPostDartEquiv r s v0)

/-- The combined-removal estimate transfers with constant one to the
literal successive-deletion graph used by the source run. -/
theorem combinedPost_countA_le_sequential (r : AppbRealization M P) (s : AppbRealization r.post Q)
    (v0 : M.atoms) {d : ℕ} (L γ δ C1 : ℝ) (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop)
    (q : Fin (r.combinedPattern s).edges.length → (Fin d → ℤ)) (scales : Finset V → ℝ) :
    appbLinkCountA (r.combinedRemoval s v0).post L γ δ C1 w
      ((r.combinedRemoval s v0).conditionedPostAdmissibility A q) scales ≤
    appbLinkCountA s.post L γ δ C1 w (combinedSequentialAdmissibility r s v0 A q) scales := by
  apply linkCountA_le_of_dart_relabeling (r.combinedRemoval s v0).post s.post
    (combinedPostDartEquiv r s v0) (combinedPost_atoms_eq r s v0)
  · intro x
    rfl
  · intro x
    rfl
  · intro x
    rfl
  · intro κ hκ
    change (r.combinedRemoval s v0).conditionedPostAdmissibility A q
      (relabelLabels (combinedPostDartEquiv r s v0) κ ∘ combinedPostDartEquiv r s v0)
    simpa only [relabelLabels,Function.comp_def,Equiv.symm_apply_apply] using hκ

end WaveTurbulence.Mole.AppbAlgorithm
