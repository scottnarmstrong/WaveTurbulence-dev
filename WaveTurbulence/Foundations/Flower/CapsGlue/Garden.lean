/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsGlue.Forest
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueLayered
/-! # A3a CAPS-GLUE: the n-ary glued garden and layered garden, with order, sign, `ζ` -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.CapsGlue
open TTree Finset WaveTurbulence.FlowerP7

variable {m w : ℕ} {a : Fin m → ℕ}

/-- The glued signature. -/
def gSigN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (sA : ∀ c, Fin (a c) → ℤˣ) : Fin w → ℤˣ :=
  fun x => sA (σ.symm x).1 (σ.symm x).2

theorem nodeSign_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (sA : ∀ c, Fin (a c) → ℤˣ) (c : Fin m)
    (x : Fin (a c) × Path) : nodeSign (gSigN σ sA) (σ ⟨c, x.1⟩, x.2) = nodeSign (sA c) x := by
  unfold nodeSign gSigN
  rw [Equiv.symm_apply_apply]

/-- The glued pairing. -/
noncomputable def gPairN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c)) :
    GLeaf (gT σ fun c => (GA c).tree) → GLeaf (gT σ fun c => (GA c).tree) := fun ℓ =>
  glueLeafN σ (fun c => (GA c).tree)
    ⟨((glueLeafN σ (fun c => (GA c).tree)).symm ℓ).1,
      (GA ((glueLeafN σ (fun c => (GA c).tree)).symm ℓ).1).pair
        ((glueLeafN σ (fun c => (GA c).tree)).symm ℓ).2⟩

/-- The glued marks. -/
noncomputable def gMarkN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c)) :
    GLeaf (gT σ fun c => (GA c).tree) → Option MarkTag := fun ℓ =>
  (GA ((glueLeafN σ (fun c => (GA c).tree)).symm ℓ).1).mark ((glueLeafN σ (fun c => (GA c).tree)).symm ℓ).2

theorem gPairN_apply (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c)) (c : Fin m)
    (x : GLeaf (GA c).tree) :
    gPairN σ GA (glueLeafN σ (fun c => (GA c).tree) ⟨c, x⟩) =
      glueLeafN σ (fun c => (GA c).tree) ⟨c, (GA c).pair x⟩ := by
  unfold gPairN
  rw [Equiv.symm_apply_apply]

theorem gMarkN_apply (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c)) (c : Fin m)
    (x : GLeaf (GA c).tree) :
    gMarkN σ GA (glueLeafN σ (fun c => (GA c).tree) ⟨c, x⟩) = (GA c).mark x := by
  unfold gMarkN
  rw [Equiv.symm_apply_apply]

/-- The glued garden. -/
@[reducible] noncomputable def glueGardenN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c)) :
    Garden w where
  sig := gSigN σ fun c => (GA c).sig
  tree := gT σ fun c => (GA c).tree
  pair := gPairN σ GA
  mark := gMarkN σ GA
  pair_pair := fun ℓ => by
    obtain ⟨⟨c, x⟩, rfl⟩ := (glueLeafN σ (fun c => (GA c).tree)).surjective ℓ
    rw [gPairN_apply, gPairN_apply, (GA c).pair_pair]
  pair_eq_iff := fun ℓ => by
    obtain ⟨⟨c, x⟩, rfl⟩ := (glueLeafN σ (fun c => (GA c).tree)).surjective ℓ
    rw [gPairN_apply, gMarkN_apply, EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq]
    simp only [heq_eq_eq, true_and]
    exact (GA c).pair_eq_iff x
  pair_sign := fun ℓ hℓ => by
    obtain ⟨⟨c, x⟩, rfl⟩ := (glueLeafN σ (fun c => (GA c).tree)).surjective ℓ
    rw [gPairN_apply] at hℓ
    simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq, heq_eq_eq, true_and] at hℓ
    have h1 := (GA c).pair_sign x hℓ
    rw [gPairN_apply]
    change nodeSign (gSigN σ fun c => (GA c).sig) (σ ⟨c, ((GA c).pair x).1.1⟩, ((GA c).pair x).1.2) =
      -nodeSign (gSigN σ fun c => (GA c).sig) (σ ⟨c, x.1.1⟩, x.1.2)
    rw [nodeSign_glueN, nodeSign_glueN]
    exact h1

theorem glueGardenN_tree (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c)) :
    (glueGardenN σ GA).tree = gT σ fun c => (GA c).tree := rfl

theorem glueN_pair_leaf (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c)) (c : Fin m)
    (x : GLeaf (GA c).tree) :
    (glueGardenN σ GA).pair (glueLeafN σ (fun c => (GA c).tree) ⟨c, x⟩) =
      glueLeafN σ (fun c => (GA c).tree) ⟨c, (GA c).pair x⟩ := gPairN_apply σ GA c x

theorem glueN_mark_leaf (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c)) (c : Fin m)
    (x : GLeaf (GA c).tree) :
    (glueGardenN σ GA).mark (glueLeafN σ (fun c => (GA c).tree) ⟨c, x⟩) = (GA c).mark x := gMarkN_apply σ GA c x

/-- The glued layering. -/
noncomputable def gLayerN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c))
    (lA : ∀ c, GNode (GA c).tree → ℕ) : GNode (glueGardenN σ GA).tree → ℕ :=
  fun x => lA ((glueNodeN σ fun c => (GA c).tree).symm x).1 ((glueNodeN σ fun c => (GA c).tree).symm x).2

@[simp] theorem gLayerN_apply (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c))
    (lA : ∀ c, GNode (GA c).tree → ℕ) (c : Fin m) (x : GNode (GA c).tree) :
    gLayerN σ GA lA (glueNodeN σ (fun c => (GA c).tree) ⟨c, x⟩) = lA c x := by
  unfold gLayerN
  rw [Equiv.symm_apply_apply]

theorem gLayerN_isLayering (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c))
    {lA : ∀ c, GNode (GA c).tree → ℕ} (hA : ∀ c, IsLayering (GA c) (lA c)) :
    IsLayering (glueGardenN σ GA) (gLayerN σ GA lA) := by
  constructor
  · intro br i
    obtain ⟨⟨c, y⟩, rfl⟩ := (glueBranchN σ fun c => (GA c).tree).surjective br
    rw [glueBranchN_child, glueBranchN_toNode, gLayerN_apply, gLayerN_apply]
    exact (hA c).1 y i
  · intro ℓ
    obtain ⟨⟨c, y⟩, rfl⟩ := (glueLeafN σ fun c => (GA c).tree).surjective ℓ
    rw [glueN_pair_leaf, glueLeafN_toNode, glueLeafN_toNode, gLayerN_apply, gLayerN_apply]
    exact (hA c).2 y

/-- The glue of layered gardens. -/
@[reducible] noncomputable def glueL (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LG : ∀ c, LayeredGarden (a c)) :
    LayeredGarden w where
  garden := glueGardenN σ fun c => (LG c).garden
  layer := gLayerN σ (fun c => (LG c).garden) fun c => (LG c).layer
  isLayering := gLayerN_isLayering σ _ fun c => (LG c).isLayering

theorem glueL_layer (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LG : ∀ c, LayeredGarden (a c)) (c : Fin m)
    (x : GNode (LG c).garden.tree) :
    (glueL σ LG).layer (glueNodeN σ (fun c => (LG c).garden.tree) ⟨c, x⟩) = (LG c).layer x :=
  gLayerN_apply σ (fun c => (LG c).garden) (fun c => (LG c).layer) c x

theorem glueN_sign (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c)) (c : Fin m)
    (x : GNode (GA c).tree) :
    (glueGardenN σ GA).sign (glueNodeN σ (fun c => (GA c).tree) ⟨c, x⟩) = (GA c).sign x := by
  show nodeSign (gSigN σ fun c => (GA c).sig) (σ ⟨c, x.1.1⟩, x.1.2) = nodeSign (GA c).sig x.1
  exact nodeSign_glueN σ _ c x.1

theorem glueN_order (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c)) :
    (glueGardenN σ GA).order = ∑ c, (GA c).order := by
  unfold Garden.order
  rw [← σ.sum_comp, Fintype.sum_sigma]
  simp [glueGardenN]

theorem glueN_zeta (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c)) :
    (glueGardenN σ GA).zeta = ∏ c, (GA c).zeta := by
  unfold Garden.zeta
  rw [← (glueBranchN σ fun c => (GA c).tree).prod_comp, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun c _ => Finset.prod_congr rfl fun x _ => ?_
  rw [glueBranchN_toNode, glueN_sign]

end WaveTurbulence.Flower.CapsGlue
