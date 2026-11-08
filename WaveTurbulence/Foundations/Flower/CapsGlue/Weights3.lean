/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsGlue.Weights2
/-! # A3a CAPS-GLUE: anchored pair-type profiles and dagger indicators of a glue are products over components -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsGlue
open TTree Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.FlowerP7 WaveTurbulence.Flower.MkDefs

variable {m w d : ℕ} {a : Fin m → ℕ}

theorem pairTrees_leaf {w : ℕ} (G : Garden w) (y : GLeaf G.tree) :
    pairTrees G y.1 = (y.1.1, (G.pair y).1.1) := by
  have hex : ∃ ℓ : GLeaf G.tree, ℓ.1 = y.1 := ⟨y, rfl⟩
  unfold pairTrees
  rw [dif_pos hex]
  have hch : hex.choose = y := Subtype.ext hex.choose_spec
  rw [hch]

theorem pairTrees_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c)) (c : Fin m)
    (y : GLeaf (LA c).garden.tree) :
    pairTrees (glueL σ LA).garden (glueLeafN σ (fun c => (LA c).garden.tree) ⟨c, y⟩).1 =
      (σ ⟨c, y.1.1⟩, σ ⟨c, ((LA c).garden.pair y).1.1⟩) := by
  have hex : ∃ ℓ : GLeaf (glueL σ LA).garden.tree,
      ℓ.1 = (glueLeafN σ (fun c => (LA c).garden.tree) ⟨c, y⟩).1 :=
    ⟨glueLeafN σ (fun c => (LA c).garden.tree) ⟨c, y⟩, rfl⟩
  unfold pairTrees
  rw [dif_pos hex]
  have hch : hex.choose = glueLeafN σ (fun c => (LA c).garden.tree) ⟨c, y⟩ := Subtype.ext hex.choose_spec
  rw [hch, show (glueL σ LA).garden.pair = (glueGardenN σ fun c => (LA c).garden).pair from rfl,
    glueN_pair_leaf]
  rfl

theorem typeProfiles_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (c : Fin m) (y : GLeaf (LA c).garden.tree) (v : Mom d) :
    typeProfiles (glueL σ LA) h (glueLeafN σ (fun c => (LA c).garden.tree) ⟨c, y⟩).1 v =
      typeProfiles (LA c) (resH σ h c) y.1 v := by
  have hn1 : (glueLeafN σ (fun c => (LA c).garden.tree) ⟨c, y⟩).1.2 ∈
      ((glueL σ LA).garden.tree (glueLeafN σ (fun c => (LA c).garden.tree) ⟨c, y⟩).1.1).nodes :=
    (glueLeafN σ (fun c => (LA c).garden.tree) ⟨c, y⟩).toNode.2
  have hn2 : y.1.2 ∈ ((LA c).garden.tree y.1.1).nodes := y.toNode.2
  unfold typeProfiles
  rw [dif_pos hn1, dif_pos hn2, pairTrees_glueN]
  have : (glueL σ LA).layer ⟨(glueLeafN σ (fun c => (LA c).garden.tree) ⟨c, y⟩).1, hn1⟩ = (LA c).layer ⟨y.1, hn2⟩ := by
    have := glueL_layer σ LA c y.toNode
    rw [← glueLeafN_toNode] at this
    exact this
  rw [this, pairTrees_leaf]
  rfl

theorem leafProdCap_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (J : Finset (Fin w)) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (k : GNode (glueL σ LA).garden.tree → Mom d) :
    leafProdCap (glueL σ LA) J h k =
      ∏ c, leafProdCap (LA c) (resJ σ J c) (resH σ h c) (resK σ (fun c => (LA c).garden.tree) k c) := by
  unfold leafProdCap
  have hI : ∀ (G : Garden w) (f : GLeaf G.tree → ℝ),
      ∏ ℓ ∈ inputLeaves G, f ℓ = ∏ ℓ : GLeaf G.tree, if ℓ ∈ inputLeaves G then f ℓ else 1 := fun G f => by
    rw [Finset.prod_ite_mem]; simp
  have hI' : ∀ c, ∀ f : GLeaf (LA c).garden.tree → ℝ,
      ∏ ℓ ∈ inputLeaves (LA c).garden, f ℓ = ∏ ℓ : GLeaf (LA c).garden.tree,
        if ℓ ∈ inputLeaves (LA c).garden then f ℓ else 1 := fun c f => by
    rw [Finset.prod_ite_mem]; simp
  rw [hI, ← (glueLeafN σ fun c => (LA c).garden.tree).prod_comp, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [hI' c]
  refine Finset.prod_congr rfl fun y _ => ?_
  have hmem : (glueLeafN σ (fun c => (LA c).garden.tree) ⟨c, y⟩ ∈ inputLeaves (glueL σ LA).garden) ↔
      y ∈ inputLeaves (LA c).garden := by
    unfold inputLeaves
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [glueLeafN_toNode, show (glueL σ LA).garden.sign = (glueGardenN σ fun c => (LA c).garden).sign from rfl,
      glueN_sign]
    exact and_congr_right fun _ => by rw [gMarkN_apply]
  by_cases hy : y ∈ inputLeaves (LA c).garden
  · rw [if_pos (hmem.2 hy), if_pos hy]
    have hc : ((glueLeafN σ (fun c => (LA c).garden.tree) ⟨c, y⟩).1.1 ∈ J ∨
        ((glueL σ LA).garden.pair (glueLeafN σ (fun c => (LA c).garden.tree) ⟨c, y⟩)).1.1 ∈ J) ↔
        (y.1.1 ∈ resJ σ J c ∨ ((LA c).garden.pair y).1.1 ∈ resJ σ J c) := by
      rw [show (glueL σ LA).garden.pair = (glueGardenN σ fun c => (LA c).garden).pair from rfl,
        glueN_pair_leaf, mem_resJ, mem_resJ]
      rfl
    by_cases hj : (y.1.1 ∈ resJ σ J c ∨ ((LA c).garden.pair y).1.1 ∈ resJ σ J c)
    · rw [if_pos (hc.2 hj), if_pos hj]
    · rw [if_neg (fun h' => hj (hc.1 h')), if_neg hj]
      have := typeProfiles_glueN σ LA h c y (k (glueLeafN σ (fun c => (LA c).garden.tree) ⟨c, y⟩).toNode)
      rw [glueLeafN_toNode] at this ⊢
      exact this
  · rw [if_neg (fun h' => hy (hmem.1 h')), if_neg hy]

theorem sibWeightCap_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (J : Finset (Fin w)) (e : Fin w → Fin 3 → Mom d) (k : GNode (glueL σ LA).garden.tree → Mom d) :
    sibWeightCap (glueL σ LA) J e k =
      ∏ c, sibWeightCap (LA c) (resJ σ J c) (fun i r => e (σ ⟨c, i⟩) r)
        (resK σ (fun c => (LA c).garden.tree) k c) := by
  unfold sibWeightCap
  rw [← (glueBranchN σ fun c => (LA c).garden.tree).prod_comp, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun c _ => Finset.prod_congr rfl fun x _ => ?_
  by_cases hp : IsCapFlowerParent (LA c) (resJ σ J c) x
  · rw [if_pos ((isCapFlowerParent_glueN σ LA J c x).2 hp), if_pos hp]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hex : (∃ ℓ : GLeaf (glueL σ LA).garden.tree, IsCapFlower (glueL σ LA) J ℓ ∧
        ℓ.toNode = (glueBranchN σ (fun c => (LA c).garden.tree) ⟨c, x⟩).child i) ↔
        (∃ ℓ : GLeaf (LA c).garden.tree, IsCapFlower (LA c) (resJ σ J c) ℓ ∧ ℓ.toNode = x.child i) := by
      rw [exists_leaf_glueN, glueBranchN_child]
      constructor
      · rintro ⟨c', y, h1, h2⟩
        rw [glueLeafN_toNode] at h2
        have := (glueNodeN σ fun c => (LA c).garden.tree).injective h2
        simp only [Sigma.mk.injEq] at this
        obtain ⟨rfl, h3⟩ := this
        exact ⟨y, (isCapFlower_glueN σ LA J c' y).1 h1, eq_of_heq h3⟩
      · rintro ⟨y, h1, h2⟩
        exact ⟨c, y, (isCapFlower_glueN σ LA J c y).2 h1, by rw [glueLeafN_toNode, h2]⟩
    by_cases hf : ∃ ℓ : GLeaf (LA c).garden.tree, IsCapFlower (LA c) (resJ σ J c) ℓ ∧ ℓ.toNode = x.child i
    · rw [if_pos (hex.2 hf), if_pos hf]
    · rw [if_neg (fun h' => hf (hex.1 h')), if_neg hf]
      rw [glueBranchN_child]
      rfl
  · rw [if_neg (mt (isCapFlowerParent_glueN σ LA J c x).1 hp), if_neg hp]

end WaveTurbulence.Flower.CapsGlue
