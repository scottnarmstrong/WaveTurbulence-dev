/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsGlue.KernelId
public import WaveTurbulence.Foundations.Flower.MkDefs.Intrinsic
/-! # A3a CAPS-GLUE: capped flowers, flower parents, intrinsic pins `fixCap` and dagger `offCap` of a glue
are the pins and dagger of the components (data read per tree). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsGlue
open TTree Finset WaveTurbulence WaveTurbulence.FlowerP7 WaveTurbulence.Flower.MkDefs

variable {m w d : ℕ} {a : Fin m → ℕ}

/-- Restriction of tree data on the glued side to component `c`. -/
def resF {α : Type*} (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (f : Fin w → α) (c : Fin m) : Fin (a c) → α :=
  fun i => f (σ ⟨c, i⟩)

/-- The caps among the trees of component `c`. -/
def resJ (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (J : Finset (Fin w)) (c : Fin m) : Finset (Fin (a c)) :=
  Finset.univ.filter fun i => σ ⟨c, i⟩ ∈ J

theorem mem_resJ (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (J : Finset (Fin w)) (c : Fin m) (i : Fin (a c)) :
    i ∈ resJ σ J c ↔ σ ⟨c, i⟩ ∈ J := by simp [resJ]

/-- Pair-type data restricted to component `c`. -/
def resH (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (c : Fin m) :
    ℕ → Fin (a c) → Fin (a c) → Mom d → ℝ := fun q i j => h q (σ ⟨c, i⟩) (σ ⟨c, j⟩)

/-- Dagger sibling data restricted to component `c`. -/
def resDag (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (dag : Option (Fin w → Fin 3 → Mom d)) (c : Fin m) :
    Option (Fin (a c) → Fin 3 → Mom d) := dag.map fun e i r => e (σ ⟨c, i⟩) r

theorem exists_branch_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree)
    (Q : GBranch (gT σ TA) → Prop) : (∃ b, Q b) ↔ ∃ (c : Fin m) (y : GBranch (TA c)), Q (glueBranchN σ TA ⟨c, y⟩) := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨⟨c, y⟩, rfl⟩ := (glueBranchN σ TA).surjective b
    exact ⟨c, y, hb⟩
  · rintro ⟨c, y, hy⟩
    exact ⟨_, hy⟩

theorem exists_leaf_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree)
    (Q : GLeaf (gT σ TA) → Prop) : (∃ b, Q b) ↔ ∃ (c : Fin m) (y : GLeaf (TA c)), Q (glueLeafN σ TA ⟨c, y⟩) := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨⟨c, y⟩, rfl⟩ := (glueLeafN σ TA).surjective b
    exact ⟨c, y, hb⟩
  · rintro ⟨c, y, hy⟩
    exact ⟨_, hy⟩

theorem sigma_val_eq_iff (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) {c c' : Fin m} (i : Fin (a c)) (i' : Fin (a c')) :
    σ ⟨c', i'⟩ = σ ⟨c, i⟩ ↔ ∃ h : c' = c, h ▸ i' = i := by
  rw [EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq]
  constructor
  · rintro ⟨rfl, h⟩; exact ⟨rfl, eq_of_heq h⟩
  · rintro ⟨rfl, h⟩; exact ⟨rfl, heq_of_eq h⟩

theorem glueN_isParentOf_same (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) (c : Fin m)
    (x : GBranch (TA c)) (y : GLeaf (TA c)) :
    (glueBranchN σ TA ⟨c, x⟩).IsParentOf (glueLeafN σ TA ⟨c, y⟩) ↔ x.IsParentOf y := by
  simp only [GBranch.IsParentOf, glueBranchN_val, glueLeafN_val, EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq,
    heq_eq_eq, true_and]

theorem glueN_not_isParentOf (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) {c c' : Fin m}
    (h : c' ≠ c) (x : GBranch (TA c)) (y : GLeaf (TA c')) :
    ¬ (glueBranchN σ TA ⟨c, x⟩).IsParentOf (glueLeafN σ TA ⟨c', y⟩) := by
  rintro ⟨h1, -⟩
  simp only [glueBranchN_val, glueLeafN_val, EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq] at h1
  exact h h1.1

theorem isCapFlower_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (J : Finset (Fin w)) (c : Fin m) (x : GLeaf (LA c).garden.tree) :
    IsCapFlower (glueL σ LA) J (glueLeafN σ (fun c => (LA c).garden.tree) ⟨c, x⟩) ↔
      IsCapFlower (LA c) (resJ σ J c) x := by
  unfold IsCapFlower
  rw [show (glueL σ LA).garden.pair = (glueGardenN σ fun c => (LA c).garden).pair from rfl, glueN_pair_leaf,
    mem_resJ, mem_resJ]
  rfl

theorem isCapFlowerParent_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (J : Finset (Fin w)) (c : Fin m) (x : GBranch (LA c).garden.tree) :
    IsCapFlowerParent (glueL σ LA) J (glueBranchN σ (fun c => (LA c).garden.tree) ⟨c, x⟩) ↔
      IsCapFlowerParent (LA c) (resJ σ J c) x := by
  unfold IsCapFlowerParent
  rw [exists_leaf_glueN]
  constructor
  · rintro ⟨c', y, h1, h2⟩
    by_cases hc : c' = c
    · subst hc
      exact ⟨y, (isCapFlower_glueN σ LA J c' y).1 h1, (glueN_isParentOf_same σ (fun c => (LA c).garden.tree) c' x y).1 h2⟩
    · exact absurd h2 (glueN_not_isParentOf σ (fun c => (LA c).garden.tree) hc x y)
  · rintro ⟨y, h1, h2⟩
    exact ⟨c, y, (isCapFlower_glueN σ LA J c y).2 h1, (glueN_isParentOf_same σ (fun c => (LA c).garden.tree) c x y).2 h2⟩

theorem fixCap_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (c : Fin m) (x : GBranch (LA c).garden.tree) :
    fixCap (glueL σ LA) J pat t s (glueBranchN σ (fun c => (LA c).garden.tree) ⟨c, x⟩) =
      fixCap (LA c) (resJ σ J c) (resF σ pat c) t s x := by
  unfold fixCap
  by_cases hp : IsCapFlowerParent (LA c) (resJ σ J c) x
  · rw [if_pos ((isCapFlowerParent_glueN σ LA J c x).2 hp), if_pos hp]
  · rw [if_neg (mt (isCapFlowerParent_glueN σ LA J c x).1 hp), if_neg hp]
    simp only [glueBranchN_val, resF]
    generalize pat (σ ⟨c, x.1.1⟩) = q
    cases q with
    | plain => rfl
    | dRoot => rfl
    | dParent =>
      refine if_congr ?_ rfl rfl
      rw [exists_branch_glueN]
      constructor
      · rintro ⟨c', y, h1, h2⟩
        by_cases hc : c' = c
        · subst hc
          exact ⟨y, (isCapFlowerParent_glueN σ LA J c' y).1 h1, (glueN_isChildOf_same σ (fun c => (LA c).garden.tree) c' y x).1 h2⟩
        · exact absurd h2 (glueN_not_isChildOf σ (fun c => (LA c).garden.tree) hc y x)
      · rintro ⟨y, h1, h2⟩
        exact ⟨c, y, (isCapFlowerParent_glueN σ LA J c y).2 h1, (glueN_isChildOf_same σ (fun c => (LA c).garden.tree) c y x).2 h2⟩
    | dChild i =>
      refine if_congr ?_ rfl rfl
      rw [exists_branch_glueN]
      constructor
      · rintro ⟨c', y, h1, h2, h3⟩
        simp only [glueBranchN_val] at h2 h3
        obtain ⟨hc, hy⟩ := (sigma_val_eq_iff σ x.1.1 y.1.1).1 h2.symm
        subst hc
        have hy' : y.1.1 = x.1.1 := hy
        exact ⟨y, (isCapFlowerParent_glueN σ LA J c' y).1 h1, hy'.symm, h3⟩
      · rintro ⟨y, h1, h2, h3⟩
        exact ⟨c, y, (isCapFlowerParent_glueN σ LA J c y).2 h1, by simp [h2], h3⟩

theorem offCap_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (J : Finset (Fin w)) (dag : Bool) :
    offCap (glueL σ LA) J dag = gOff σ (fun c => (LA c).garden.tree) (fun c => offCap (LA c) (resJ σ J c) dag) := by
  ext b
  obtain ⟨⟨c, x⟩, rfl⟩ := (glueBranchN σ fun c => (LA c).garden.tree).surjective b
  rw [mem_gOff]
  unfold offCap
  cases dag <;> simp [isCapFlowerParent_glueN]

end WaveTurbulence.Flower.CapsGlue
