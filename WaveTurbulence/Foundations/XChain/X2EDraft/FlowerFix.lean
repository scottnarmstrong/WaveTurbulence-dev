/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FTreeLeaf

/-!
# X2E-3, step 4: the designated times and removed phases of the flower graft

**Flower data at given flower trees** (`FlowerAt P p tops`): flower graft data whose top forest is literally
`ftop tops` and whose flowers are the flowers of `tops`; `FlowerAt.toData` (for flower signs `ζ`).

**Statements** (for `D : FlowerGraftData`):
- `isFlowerParent_iff`: a branch of the flower graft is a flower parent iff the flower path of its tree is its path
  followed by one step.
- `not_isFlowerParent_lower`, `lower_path_ne_nil`: a lower branch is not a flower parent, and (non-trivial top
  trees) is not a root.
- For `x : FlowerAt`, the gate's designated times `fixPat` (patterns `plain`, `dRoot`) and removed phases are, on top
  branches, `fixFl`/`offFl` of X2E-3 step 2, and trivial on lower branches (`fixPat_top`, `fixPat_lower`,
  `off_top`, `off_lower`).
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset Induct SysAPI
open scoped Classical

/-! ## General flower graft data -/

namespace FlowerGraftData

variable {Pm p : ℕ} {ζ : ℤˣ} (D : FlowerGraftData Pm p ζ)

theorem isFlower_iff (ℓ : GLeaf D.flowerGraft.garden.tree) :
    D.flowerGraft.garden.IsFlower ℓ ↔ ℓ.1.2 = D.fl ℓ.1.1 := by
  constructor
  · intro h
    have hm : D.flowerGraft.garden.mark ℓ ≠ none := by
      rw [h]
      simp
    have he := D.eq_flLeaf_of_marked hm
    have hv := congrArg Subtype.val he
    rw [D.flLeaf_val] at hv
    exact congrArg Prod.snd hv
  · intro h
    have he : ℓ = D.flLeaf ℓ.1.1 := Subtype.ext (by rw [D.flLeaf_val]; exact Prod.ext rfl h)
    rw [he]
    exact D.mark_eq_equal_of_ne_none (D.mark_flLeaf _)

theorem isFlowerParent_iff (b : GBranch D.flowerGraft.garden.tree) :
    D.flowerGraft.garden.IsFlowerParent b ↔ ∃ i : Fin 3, D.fl b.1.1 = b.1.2 ++ [i] := by
  constructor
  · rintro ⟨ℓ, hℓ, hj, i, hi⟩
    have h := (D.isFlower_iff ℓ).mp hℓ
    rw [hj] at h
    exact ⟨i, h.symm.trans hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨D.flLeaf b.1.1, D.mark_eq_equal_of_ne_none (D.mark_flLeaf _), ?_, i, ?_⟩
    · rw [D.flLeaf_val]
    · rw [D.flLeaf_val]
      exact hi

/-- The branches of the flower graft, as the graft forest's branches. -/
abbrev GBr :=
  GBranch (graftForest D.base.top (blockGraftTrees D.base.top D.base.partition (fun B => (D.lowFl B).garden)))

theorem isFlowerParent_iff' (b : D.GBr) :
    D.flowerGraft.garden.IsFlowerParent b ↔ ∃ i : Fin 3, D.fl b.1.1 = b.1.2 ++ [i] :=
  D.isFlowerParent_iff b

/-- A lower branch is not a flower parent. -/
theorem not_isFlowerParent_lower (B : D.base.partition.parts) (c : GBranch (D.lowFl B).garden.tree) :
    ¬ D.flowerGraft.garden.IsFlowerParent
      (gardenBranchEquiv D.base.top D.base.partition (fun B => (D.lowFl B).garden) (.inr ⟨B, c⟩)) := by
  rw [D.isFlowerParent_iff']
  rintro ⟨i, hi⟩
  have hv := gardenBranchEquiv_lower_val D.base.top D.base.partition (fun B => (D.lowFl B).garden) B c
  rw [hv] at hi
  set ℓ := (blockRootEquiv D.base.top D.base.partition).symm ⟨B, c.1.1⟩
  change D.fl ℓ.1.1 = (ℓ.1.2 ++ c.1.2) ++ [i] at hi
  have hpre : ℓ.1.2 <+: D.fl ℓ.1.1 := by
    rw [hi, List.append_assoc]
    exact List.prefix_append _ _
  have heq := leaf_eq_of_prefix _ ℓ.2 (D.fl_mem ℓ.1.1) hpre
  rw [heq, List.append_assoc] at hi
  have h0 := congrArg List.length hi
  simp at h0

/-- With non-trivial top trees, a lower branch is not a root. -/
theorem lower_path_ne_nil (htop : ∀ j, D.base.top j ≠ TTree.leaf) (B : D.base.partition.parts)
    (c : GBranch (D.lowFl B).garden.tree) :
    (gardenBranchEquiv D.base.top D.base.partition (fun B => (D.lowFl B).garden) (.inr ⟨B, c⟩)).1.2 ≠ [] := by
  rw [gardenBranchEquiv_lower_val]
  intro h
  set ℓ := (blockRootEquiv D.base.top D.base.partition).symm ⟨B, c.1.1⟩
  change ℓ.1.2 ++ c.1.2 = [] at h
  have h0 : ℓ.1.2 = [] := (List.append_eq_nil_iff.mp h).1
  have hl := ℓ.2
  rw [h0] at hl
  exact htop _ (eq_leaf_of_nil_mem_leaves hl)

end FlowerGraftData

/-! ## Flower data at given flower trees -/

/-- **Flower graft data at the flower trees `tops`.** -/
structure FlowerAt (Pm p : ℕ) (tops : Fin (2 * Pm) → FTree) where
  partition : Finpartition (univ : Finset (GLeaf (ftop tops)))
  low : (B : partition.parts) → LayeredGarden B.1.card
  plain : ∀ B, (low B).garden.IsPlain
  sign : ∀ B k, (low B).garden.sig k = nodeSign (altFlowerSig Pm) ((blockRootEquiv (ftop tops) partition).symm ⟨B, k⟩).1
  component : ∀ B, IsCanonG p (low B) ∨
    B.1.card = 2 ∧ (∀ k, (low B).garden.tree k = TTree.leaf) ∧ ∀ a, (low B).layer a = p
  pair_mem : ∀ j, ({⟨(j, (tops j).flowerPath), (tops j).flowerPath_mem_leaves⟩,
    ⟨(partner j, (tops (partner j)).flowerPath), (tops (partner j)).flowerPath_mem_leaves⟩} :
      Finset (GLeaf (ftop tops))) ∈ partition.parts

namespace FlowerAt

variable {Pm p : ℕ} {tops : Fin (2 * Pm) → FTree} (x : FlowerAt Pm p tops)

/-- The plain graft data. -/
abbrev base : PlainGraftData (altFlowerSig Pm) p := ⟨ftop tops, x.partition, x.low, x.plain, x.sign, x.component⟩

omit x in
theorem fl_sign {ζ : ℤˣ} (hsign : ∀ j, (tops j).sign = ζ) (j : Fin (2 * Pm)) :
    TTree.pathSign (altFlowerSig Pm j) (tops j).flowerPath = ζ * altFlowerSig Pm j := by
  have h := sign_eq_pathSign (tops j)
  rw [hsign j] at h
  unfold TTree.pathSign at h ⊢
  rw [one_mul] at h
  rw [← h, mul_comm]

/-- **The flower graft data.** -/
abbrev toData {ζ : ℤˣ} (hsign : ∀ j, (tops j).sign = ζ) : FlowerGraftData Pm p ζ where
  base := x.base
  fl := fun j => (tops j).flowerPath
  fl_mem := fun j => (tops j).flowerPath_mem_leaves
  fl_sign := FlowerAt.fl_sign hsign
  pair_mem := x.pair_mem

end FlowerAt

/-! ## The gate's data on the flower graft -/

section Gate

variable {Pm p : ℕ} {ζ : ℤˣ} {tops : Fin (2 * Pm) → FTree} (hF : ∀ j, tops j ≠ FTree.flower)
  (x : FlowerAt Pm p tops) (hsign : ∀ j, (tops j).sign = ζ)

omit hF in
theorem mem_filter_isFlowerParent {w : ℕ} (G : Garden w) (z : GBranch G.tree) :
    z ∈ univ.filter G.IsFlowerParent ↔ G.IsFlowerParent z := by
  simp

/-- The path of the flower parent. -/
theorem exists_flower_step_iff (j : Fin (2 * Pm)) (q : TTree.Path) :
    (∃ i : Fin 3, (tops j).flowerPath = q ++ [i]) ↔ q = ((tops j).flowerParent (hF j)).1.2 := by
  have hne := FTree.flowerPath_ne_nil (hF j)
  change _ ↔ q = (tops j).flowerPath.dropLast
  constructor
  · rintro ⟨i, hi⟩
    rw [hi, List.dropLast_concat]
  · intro hq
    refine ⟨(tops j).flowerPath.getLast hne, ?_⟩
    rw [hq, List.dropLast_append_getLast hne]

include hF in
theorem top_ne_leaf (j : Fin (2 * Pm)) : ftop tops j ≠ TTree.leaf := (ne_flower_iff _).mp (hF j)

theorem isFlowerParent_top (b : GBranch (ftop tops)) :
    (x.toData hsign).flowerGraft.garden.IsFlowerParent
      (gardenBranchEquiv (x.toData hsign).base.top (x.toData hsign).base.partition
        (fun B => ((x.toData hsign).lowFl B).garden) (.inl b)) ↔
      b.1.2 = ((tops b.1.1).flowerParent (hF b.1.1)).1.2 := by
  rw [FlowerGraftData.isFlowerParent_iff', gardenBranchEquiv_top_val]
  exact exists_flower_step_iff hF b.1.1 b.1.2

theorem toSingle_eq_iff (b : GBranch (ftop tops)) :
    toSingle tops b = (tops b.1.1).flowerParent (hF b.1.1) ↔
      b.1.2 = ((tops b.1.1).flowerParent (hF b.1.1)).1.2 := by
  constructor
  · intro h
    exact congrArg (fun c : GBranch (single (tops b.1.1).toTree) => c.1.2) h
  · intro h
    exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) h)

/-- **The designated times on top branches.** -/
theorem fixPat_top (pat : FixPat) (hpat : pat = .plain ∨ pat = .dRoot) (t s : ℝ) (b : GBranch (ftop tops)) :
    (x.toData hsign).flowerGraft.fixPat (fun _ => pat) t s
      (gardenBranchEquiv (x.toData hsign).base.top (x.toData hsign).base.partition
        (fun B => ((x.toData hsign).lowFl B).garden) (.inl b)) =
      fixFl tops hF pat t s b := by
  have hfp := isFlowerParent_top hF x hsign b
  have hval := gardenBranchEquiv_top_val (x.toData hsign).base.top (x.toData hsign).base.partition
    (fun B => ((x.toData hsign).lowFl B).garden) b
  have hts := toSingle_eq_iff hF b
  unfold LayeredGarden.fixPat fixFl treeFixPat
  by_cases h : b.1.2 = ((tops b.1.1).flowerParent (hF b.1.1)).1.2
  · rw [ite_eq_left (hfp.mpr h), ite_eq_left (hts.mpr h)]
  · rw [ite_eq_right (fun h' => h (hfp.mp h')), ite_eq_right (fun h' => h (hts.mp h'))]
    rcases hpat with rfl | rfl
    · rfl
    · simp only [hval]
      rfl

include hF in
/-- **The designated times on lower branches.** -/
theorem fixPat_lower (pat : FixPat) (hpat : pat = .plain ∨ pat = .dRoot) (t s : ℝ)
    (B : (x.toData hsign).base.partition.parts) (c : GBranch ((x.toData hsign).lowFl B).garden.tree) :
    (x.toData hsign).flowerGraft.fixPat (fun _ => pat) t s
      (gardenBranchEquiv (x.toData hsign).base.top (x.toData hsign).base.partition
        (fun B => ((x.toData hsign).lowFl B).garden) (.inr ⟨B, c⟩)) = none := by
  have hnf := (x.toData hsign).not_isFlowerParent_lower B c
  unfold LayeredGarden.fixPat
  rw [ite_eq_right hnf]
  rcases hpat with rfl | rfl
  · rfl
  · have hne := (x.toData hsign).lower_path_ne_nil (fun j => top_ne_leaf hF j) B c
    exact ite_eq_right hne

/-- **The removed phases on top branches.** -/
theorem off_top {d : ℕ} (dagger : Option (Fin 3 → Mom d)) (b : GBranch (ftop tops)) :
    gardenBranchEquiv (x.toData hsign).base.top (x.toData hsign).base.partition
        (fun B => ((x.toData hsign).lowFl B).garden) (.inl b) ∈
      (if dagger.isSome then univ.filter (x.toData hsign).flowerGraft.garden.IsFlowerParent else ∅) ↔
      b ∈ offFl tops hF dagger := by
  rw [mem_offFl]
  by_cases h : dagger.isSome
  · rw [ite_eq_left h]
    exact (mem_filter_isFlowerParent _ _).trans ((isFlowerParent_top hF x hsign b).trans (and_iff_right h).symm)
  · rw [ite_eq_right h]
    exact iff_of_false (notMem_empty _) (fun hh => h hh.1)

/-- **No removed phases on lower branches.** -/
theorem off_lower {d : ℕ} (dagger : Option (Fin 3 → Mom d)) (B : (x.toData hsign).base.partition.parts)
    (c : GBranch ((x.toData hsign).lowFl B).garden.tree) :
    gardenBranchEquiv (x.toData hsign).base.top (x.toData hsign).base.partition
        (fun B => ((x.toData hsign).lowFl B).garden) (.inr ⟨B, c⟩) ∉
      (if dagger.isSome then univ.filter (x.toData hsign).flowerGraft.garden.IsFlowerParent else ∅) := by
  by_cases h : dagger.isSome
  · rw [ite_eq_left h]
    exact fun hm => (x.toData hsign).not_isFlowerParent_lower B c ((mem_filter_isFlowerParent _ _).mp hm)
  · rw [ite_eq_right h]
    exact notMem_empty _

end Gate

end WaveTurbulence.X2E
