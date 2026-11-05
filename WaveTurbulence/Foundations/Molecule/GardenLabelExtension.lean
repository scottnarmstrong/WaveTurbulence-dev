/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.GardenIncidence
import Mathlib.Tactic

/-!
# Recovering node labels from bond labels and prescribed roots

TARGET `defdecmol`, with the root-pair compatibility ruling F52. These
maps are generic in the label carrier; conservation is treated separately.
-/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} {E : Type*} (G : Garden w)

/-- The actual node attached to an incidence of a garden bond. -/
@[expose] def dartNode : GardenDart G → GNode G.tree
  | .inl (c,_) => c.1.toNode
  | .inr l => l.1.toNode

/-- Directly paired roots must have equal prescribed values (F52). -/
@[expose] def RootPairCompatible (n : Fin w → E) : Prop :=
  ∀ l : GLeaf G.tree, l.1.2 = [] → (G.pair l).1.2 = [] → n l.1.1 = n (G.pair l).1.1

/-- Restriction of node labels to the actual bond incidences. -/
@[expose] def restrictLabels (κ : GNode G.tree → E) : GardenDart G → E :=
  fun x => κ (dartNode G x)

/-- Recover every node label from a bond-constant assignment and the roots.
A nonroot leaf paired to a root receives that prescribed root value. -/
@[expose] def extendLabels (hP : G.IsPlain) (n : Fin w → E)
    (k : GardenDart G → E) (a : GNode G.tree) : E :=
  if hr : a.1.2 = [] then n a.1.1
  else if hb : a.1.2 ∈ (G.tree a.1.1).branching then
    k (.inl (⟨⟨a.1,hb⟩,hr⟩,false))
  else
    let l : GLeaf G.tree := ⟨a.1, ((TTree.mem_nodes_iff _ _).mp a.2).resolve_right hb⟩
    if hp : (G.pair l).1.2 = [] then n (G.pair l).1.1
    else k (.inr ⟨l,hP l,hr,hp⟩)

theorem extendLabels_root (hP : G.IsPlain) (n : Fin w → E) (k : GardenDart G → E)
    (i : Fin w) : extendLabels G hP n k (GNode.root G.tree i) = n i := by
  simp [extendLabels,GNode.root]

theorem extendLabels_branch (hP : G.IsPlain) (n : Fin w → E) (k : GardenDart G → E)
    (b : GBranch G.tree) (hb : b.1.2 ≠ []) :
    extendLabels G hP n k b.toNode = k (.inl (⟨b,hb⟩,false)) := by
  simp [extendLabels,GBranch.toNode,hb,b.2]
  rfl

theorem extendLabels_leaf (hP : G.IsPlain) (n : Fin w → E) (k : GardenDart G → E)
    (l : GLeaf G.tree) (hl : l.1.2 ≠ []) (hp : (G.pair l).1.2 ≠ []) :
    extendLabels G hP n k l.toNode = k (.inr ⟨l,hP l,hl,hp⟩) := by
  have hb : l.1.2 ∉ (G.tree l.1.1).branching :=
    TTree.not_mem_branching_of_mem_leaves _ l.2
  dsimp only [extendLabels,GLeaf.toNode]
  rw [dite_eq_right hl,dite_eq_right hb]
  change (if hp' : (G.pair l).1.2 = [] then n (G.pair l).1.1
    else k (.inr ⟨l,hP l,hl,hp'⟩)) = _
  simp only [hp, ↓reduceDIte]

theorem extendLabels_leaf_paired_root (hP : G.IsPlain) (n : Fin w → E)
    (k : GardenDart G → E) (l : GLeaf G.tree) (hl : l.1.2 ≠ [])
    (hp : (G.pair l).1.2 = []) :
    extendLabels G hP n k l.toNode = n (G.pair l).1.1 := by
  have hb : l.1.2 ∉ (G.tree l.1.1).branching :=
    TTree.not_mem_branching_of_mem_leaves _ l.2
  dsimp only [extendLabels,GLeaf.toNode]
  rw [dite_eq_right hl,dite_eq_right hb]
  change (if hp' : (G.pair l).1.2 = [] then n (G.pair l).1.1
    else k (.inr ⟨l,hP l,hl,hp'⟩)) = _
  simp only [hp, ↓reduceDIte]

/-- Restricting an extension recovers every actual bond label. -/
theorem restrict_extendLabels (hP : G.IsPlain) (n : Fin w → E) (k : GardenDart G → E)
    (hk : ∀ x, k (G.molecule.mate x) = k x) :
    restrictLabels G (extendLabels G hP n k) = k := by
  funext x
  rcases x with ⟨c,b⟩ | l
  · cases b
    · exact extendLabels_branch G hP n k c.1 c.2
    · change extendLabels G hP n k c.1.toNode = k (.inl (c,true))
      rw [extendLabels_branch]
      exact hk (.inl (c,true))
  · exact extendLabels_leaf G hP n k l.1 l.2.2.1 l.2.2.2

/-- A restriction is constant across every actual mate. -/
theorem restrictLabels_mate (κ : GNode G.tree → E)
    (hκ : ∀ l : GLeaf G.tree, κ l.toNode = κ (G.pair l).toNode) :
    ∀ x, restrictLabels G κ (G.molecule.mate x) = restrictLabels G κ x := by
  rintro (⟨c,b⟩ | l)
  · cases b <;> rfl
  · exact (hκ l.1).symm

/-- Extending the restriction recovers every node label. -/
theorem extend_restrictLabels (hP : G.IsPlain) (n : Fin w → E)
    (κ : GNode G.tree → E) (hr : ∀ i, κ (GNode.root G.tree i) = n i)
    (hκ : ∀ l : GLeaf G.tree, κ l.toNode = κ (G.pair l).toNode) :
    extendLabels G hP n (restrictLabels G κ) = κ := by
  funext a
  by_cases ha : a.1.2 = []
  · have he : a = GNode.root G.tree a.1.1 := Subtype.ext (Prod.ext rfl ha)
    rw [he,extendLabels_root,hr]
  · by_cases hb : a.1.2 ∈ (G.tree a.1.1).branching
    · exact extendLabels_branch G hP n _ ⟨a.1,hb⟩ ha
    · let l : GLeaf G.tree := ⟨a.1, ((TTree.mem_nodes_iff _ _).mp a.2).resolve_right hb⟩
      change extendLabels G hP n (restrictLabels G κ) l.toNode = κ l.toNode
      by_cases hp : (G.pair l).1.2 = []
      · rw [extendLabels_leaf_paired_root G hP n _ l ha hp,hκ l]
        have he : (G.pair l).toNode = GNode.root G.tree (G.pair l).1.1 :=
          Subtype.ext (Prod.ext rfl hp)
        rw [he,hr]
      · exact extendLabels_leaf G hP n _ l ha hp

/-- Root compatibility is exactly the extra condition needed to recover all
leaf-pair equations, including pairs of trivial trees. -/
theorem extendLabels_paired (hP : G.IsPlain) (n : Fin w → E)
    (hn : RootPairCompatible G n) (k : GardenDart G → E)
    (hk : ∀ x, k (G.molecule.mate x) = k x) (l : GLeaf G.tree) :
    extendLabels G hP n k l.toNode = extendLabels G hP n k (G.pair l).toNode := by
  have root_val (a : GLeaf G.tree) (ha : a.1.2 = []) :
      extendLabels G hP n k a.toNode = n a.1.1 := by
    have he : a.toNode = GNode.root G.tree a.1.1 := Subtype.ext (Prod.ext rfl ha)
    rw [he,extendLabels_root]
  by_cases hl : l.1.2 = []
  · rw [root_val l hl]
    by_cases hp : (G.pair l).1.2 = []
    · rw [root_val (G.pair l) hp]
      exact hn l hl hp
    · rw [extendLabels_leaf_paired_root G hP n k (G.pair l) hp
        (by rw [G.pair_pair]; exact hl),G.pair_pair]
  · by_cases hp : (G.pair l).1.2 = []
    · rw [extendLabels_leaf_paired_root G hP n k l hl hp,root_val (G.pair l) hp]
    · rw [extendLabels_leaf G hP n k l hl hp,
        extendLabels_leaf G hP n k (G.pair l) hp (by rw [G.pair_pair]; exact hl)]
      exact (hk (.inr ⟨l,hP l,hl,hp⟩)).symm

/-- The root-pair compatibility is necessary for any fixed-root garden label
assignment satisfying its leaf-pair equations. -/
theorem rootPairCompatible_of_labels (n : Fin w → E) (κ : GNode G.tree → E)
    (hr : ∀ i, κ (GNode.root G.tree i) = n i)
    (hκ : ∀ l : GLeaf G.tree, κ l.toNode = κ (G.pair l).toNode) :
    RootPairCompatible G n := by
  intro l hl hp
  have he (a : GLeaf G.tree) (ha : a.1.2 = []) :
      a.toNode = GNode.root G.tree a.1.1 := Subtype.ext (Prod.ext rfl ha)
  have hh := hκ l
  rw [he l hl,he (G.pair l) hp,hr,hr] at hh
  exact hh

end WaveTurbulence.Mole
