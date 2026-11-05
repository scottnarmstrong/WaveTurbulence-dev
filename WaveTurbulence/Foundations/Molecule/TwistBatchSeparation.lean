/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistFamilyBatch

/-! # Distinct source subsets give distinct actual gardens

A shallowest lower joint in the symmetric difference witnesses the
change: it remains a branch under one subset, and becomes a leaf under
the other. This rules out identifications after forgetting the transported
family, including when some attached free subtrees happen to coincide.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} {ι : Type*}

/-- A literal leaf at the specified raw address. -/
@[expose] def LeafAt (G : Garden w) (x : Fin w × Path) : Prop := x.2 ∈ (G.tree x.1).leaves

/-- A literal branching node at the specified raw address. -/
@[expose] def BranchAt (G : Garden w) (x : Fin w × Path) : Prop := x.2 ∈ (G.tree x.1).branching

/-- A literal leaf and branch at the same address distinguish two gardens. -/
theorem gardens_ne_of_leaf_branch {G H : Garden w} {x : Fin w × Path}
    (hl : LeafAt G x) (hb : BranchAt H x) : G ≠ H := by
  intro he
  subst H
  exact leaf_not_prefix_branch hl hb ⟨[],List.append_nil _⟩

/-- A shortest selected lower path cannot have another selected lower as an ancestor. -/
theorem CoreFamily.shallowest_outside {G : Garden w} (F : CoreFamily G ι) {U : Finset ι} {j : ι}
    (hmin : ∀ i ∈ U, (F.placement j).lower.1.2.length ≤ (F.placement i).lower.1.2.length)
    {i : ι} (hi : i ∈ U) (hne : i ≠ j) :
    ¬ (F.placement i).lower.toNode.IsDesc (F.placement j).lower.toNode := by
  intro hd
  have he : (F.placement i).lower = (F.placement j).lower := by
    apply Subtype.ext
    exact Prod.ext hd.1 (hd.2.eq_of_length (Nat.le_antisymm hd.2.length_le (hmin i hi)))
  exact hne (F.lower_injective he)

variable [DecidableEq ι]

/-- The active shallowest member leaves a literal leaf at its old lower address. -/
theorem familyBatch_leaf_at_shallowest (S : Finset ι) (s : FamilyState w ι) {j : ι} (hj : j ∈ S)
    (hout : ∀ i ∈ S, i ≠ j → ¬ (s.2.placement i).lower.toNode.IsDesc (s.2.placement j).lower.toNode) :
    LeafAt (familyBatch S s).1 (s.2.placement j).lower.1 := by
  classical
  let t := familyBatch (S.erase j) s
  have hv : (t.2.placement j).lower.1 = (s.2.placement j).lower.1 :=
    (familyBatch_protected (S.erase j) s j (fun i hi =>
      hout i (Finset.mem_erase.mp hi).2 (Finset.mem_erase.mp hi).1)).1
  have hlast : familyBatch S s = familyStep j t := by
    have h := familyBatch_insert_last (Finset.notMem_erase j S) s
    exact (congrArg (fun S => familyBatch S s) (Finset.insert_erase hj).symm).trans h
  have hl : LeafAt (familyStep j t).1 (t.2.placement j).lower.1 := unitTwist_leaf_at_lower (t.2.placement j)
  have hleaf : LeafAt (familyStep j t).1 (s.2.placement j).lower.1 := hv ▸ hl
  exact hlast.symm ▸ hleaf

/-- An inactive shallowest member keeps a literal branch at its old lower address. -/
theorem familyBatch_branch_at_protected (T : Finset ι) (s : FamilyState w ι) (j : ι)
    (hout : ∀ i ∈ T, ¬ (s.2.placement i).lower.toNode.IsDesc (s.2.placement j).lower.toNode) :
    BranchAt (familyBatch T s).1 (s.2.placement j).lower.1 := by
  have hv := (familyBatch_protected T s j hout).1
  have hb : BranchAt (familyBatch T s).1 ((familyBatch T s).2.placement j).lower.1 :=
    ((familyBatch T s).2.placement j).lower.2
  exact hv ▸ hb

/-- Nonempty disjoint subsets give different literal gardens. -/
theorem familyBatch_disjoint_garden_ne (S T : Finset ι) (hST : Disjoint S T)
    (hne : (S ∪ T).Nonempty) (s : FamilyState w ι) : (familyBatch S s).1 ≠ (familyBatch T s).1 := by
  classical
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image (S ∪ T)
    (fun i => (s.2.placement i).lower.1.2.length) hne
  have hout {i : ι} (hi : i ∈ S ∪ T) (hij : i ≠ j) := s.2.shallowest_outside hmin hi hij
  rcases Finset.mem_union.mp hj with hjS | hjT
  · have hnjT : j ∉ T := fun h => Finset.disjoint_left.mp hST hjS h
    exact gardens_ne_of_leaf_branch
      (familyBatch_leaf_at_shallowest S s hjS (fun i hi hij => hout (Finset.mem_union_left T hi) hij))
      (familyBatch_branch_at_protected T s j (fun i hi => hout (Finset.mem_union_right S hi) (fun he => hnjT (he ▸ hi))))
  · have hnjS : j ∉ S := fun h => Finset.disjoint_left.mp hST h hjT
    exact Ne.symm (gardens_ne_of_leaf_branch
      (familyBatch_leaf_at_shallowest T s hjT (fun i hi hij => hout (Finset.mem_union_right S hi) hij))
      (familyBatch_branch_at_protected S s j (fun i hi => hout (Finset.mem_union_left T hi) (fun he => hnjS (he ▸ hi)))))

end WaveTurbulence.Twist
