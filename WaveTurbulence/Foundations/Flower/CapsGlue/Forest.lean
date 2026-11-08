/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueForest
/-! # A3a CAPS-GLUE: the n-ary glue of forests along `σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w`

The n-ary analogue of FLOWER-P7's binary `glueNode/glueLeaf/glueBranch` (which handles `Fin a ⊕ Fin b`). The glued
forest has `T (σ ⟨c, i⟩) = TA c i`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.CapsGlue
open TTree Finset WaveTurbulence.FlowerP7

variable {m w : ℕ} {a : Fin m → ℕ}

/-- The glued forest. -/
def gT (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) : Fin w → TTree :=
  fun x => TA (σ.symm x).1 (σ.symm x).2

@[simp] theorem gT_apply (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) (c : Fin m)
    (i : Fin (a c)) : gT σ TA (σ ⟨c, i⟩) = TA c i := by
  unfold gT
  rw [Equiv.symm_apply_apply]

/-- The map of `glueSubN`. -/
def glueSubMapN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) (S : TTree → Finset Path) :
    (Σ c : Fin m, SubSet (TA c) S) → SubSet (gT σ TA) S
  | ⟨c, x⟩ => ⟨(σ ⟨c, x.1.1⟩, x.1.2), by simpa using x.2⟩

theorem glueSubMapN_bijective (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree)
    (S : TTree → Finset Path) : Function.Bijective (glueSubMapN σ TA S) := by
  constructor
  · rintro ⟨c, x⟩ ⟨c', y⟩ h
    have h' := congrArg Subtype.val h
    simp only [glueSubMapN, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq] at h'
    obtain ⟨⟨rfl, h1⟩, h2⟩ := h'
    have h1 : x.1.1 = y.1.1 := eq_of_heq h1
    exact congrArg (Sigma.mk c) (Subtype.ext (Prod.ext h1 h2))
  · rintro ⟨⟨z, p⟩, hp⟩
    obtain ⟨⟨c, i⟩, rfl⟩ := σ.surjective z
    exact ⟨⟨c, ⟨(i, p), by simpa using hp⟩⟩, rfl⟩

/-- Generic equivalence for nodes, leaves, branching nodes of the glued forest. -/
noncomputable def glueSubN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree)
    (S : TTree → Finset Path) : (Σ c : Fin m, SubSet (TA c) S) ≃ SubSet (gT σ TA) S :=
  Equiv.ofBijective _ (glueSubMapN_bijective σ TA S)

noncomputable def glueNodeN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) :
    (Σ c : Fin m, GNode (TA c)) ≃ GNode (gT σ TA) := glueSubN σ TA TTree.nodes

noncomputable def glueLeafN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) :
    (Σ c : Fin m, GLeaf (TA c)) ≃ GLeaf (gT σ TA) := glueSubN σ TA TTree.leaves

noncomputable def glueBranchN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) :
    (Σ c : Fin m, GBranch (TA c)) ≃ GBranch (gT σ TA) := glueSubN σ TA TTree.branching

@[simp] theorem glueNodeN_val (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) (c : Fin m)
    (x : GNode (TA c)) : (glueNodeN σ TA ⟨c, x⟩).1 = (σ ⟨c, x.1.1⟩, x.1.2) := rfl
@[simp] theorem glueLeafN_val (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) (c : Fin m)
    (x : GLeaf (TA c)) : (glueLeafN σ TA ⟨c, x⟩).1 = (σ ⟨c, x.1.1⟩, x.1.2) := rfl
@[simp] theorem glueBranchN_val (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) (c : Fin m)
    (x : GBranch (TA c)) : (glueBranchN σ TA ⟨c, x⟩).1 = (σ ⟨c, x.1.1⟩, x.1.2) := rfl

theorem glueBranchN_toNode (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) (c : Fin m)
    (x : GBranch (TA c)) : (glueBranchN σ TA ⟨c, x⟩).toNode = glueNodeN σ TA ⟨c, x.toNode⟩ := rfl
theorem glueLeafN_toNode (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) (c : Fin m)
    (x : GLeaf (TA c)) : (glueLeafN σ TA ⟨c, x⟩).toNode = glueNodeN σ TA ⟨c, x.toNode⟩ := rfl

theorem glueBranchN_child (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) (c : Fin m)
    (x : GBranch (TA c)) (i : Fin 3) :
    (glueBranchN σ TA ⟨c, x⟩).child i = glueNodeN σ TA ⟨c, x.child i⟩ := by
  apply Subtype.ext
  rfl

end WaveTurbulence.Flower.CapsGlue
