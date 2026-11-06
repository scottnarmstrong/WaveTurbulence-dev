/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.GlueGarden

/-!
# Gluing decorations

In the gluing situation `GlueData G G₁ G₂ X`, a decoration of `G` with zero root values is a pair of
decorations of `G₁` and `G₂` with zero root values (`GlueData.decEquiv`): restriction along the node maps
`ι₁`, `ι₂`, and conversely the glued function `GlueData.glue`. The lone leaf of `G₁` carries the value of
its root (`GlueData.lone_eq_root`, conservation, LINKS `chainDec_lone_eq`), which is `0`, as is the root
`0` of `G₂`, so the two pieces agree at the junction.

The two decoration conditions (`DecSplit`, `DecGlue`) are proved for each instance from the code
(`CplDec`, `ChainDec`).
-/

@[expose] public section

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.Links WaveTurbulence.Reg

variable {w : ℕ} [NeZero w]

namespace GlueData

variable {G : Garden w} {G₁ : Garden 1} {G₂ : Garden w} {X : RegChain}
variable (h : GlueData G G₁ G₂ X)

/-- The lone leaf of the top paired tree. -/
def lone : GNode G₁.tree :=
  ⟨((0 : Fin 1), X.lonePath), by
    rw [show ((0 : Fin 1), X.lonePath).1 = 0 from rfl, h.tree1]
    exact lonePath_mem_plug X _ _⟩

/-- **Conservation**: the lone leaf of a decoration of the top paired tree carries the root value. -/
theorem lone_eq_root {V : Type*} [AddCommGroup V] {κ₁ : GNode G₁.tree → V}
    (hκ : IsDecoration G₁ κ₁) : κ₁ h.lone = κ₁ (GNode.root G₁.tree 0) := by
  have hc := chainDec_of_decoration h.dec1 hκ
  have := chainDec_lone_eq _ X _ _ hc
  have e1 : extend κ₁ ((0 : Fin 1), ([] : Path)) = κ₁ (GNode.root G₁.tree 0) :=
    extend_node κ₁ (GNode.root G₁.tree 0)
  have e2 : extend κ₁ (addrExt ((0 : Fin 1), ([] : Path)) X.lonePath) = κ₁ h.lone := by
    have : addrExt ((0 : Fin 1), ([] : Path)) X.lonePath = h.lone.1 := by simp [addrExt, lone]
    rw [this]
    exact extend_node κ₁ h.lone
  rw [← e1, ← e2, this]

theorem ι₁_root : h.ι₁ (GNode.root G₁.tree 0) = GNode.root G.tree 0 := rfl

theorem ι₁_lone : h.ι₁ h.lone = h.ι₂ (GNode.root G₂.tree 0) := by
  apply Subtype.ext
  show ((0 : Fin w), X.lonePath) = botAddr X.lonePath ((0 : Fin w), [])
  simp [botAddr]

theorem ι₂_root {j : Fin w} (hj : j ≠ 0) : h.ι₂ (GNode.root G₂.tree j) = GNode.root G.tree j := by
  apply Subtype.ext
  show botAddr X.lonePath (j, []) = (j, [])
  simp [botAddr, hj]

/-- The glued function on the addresses of `G`. -/
noncomputable def glueAddr {V : Type*} [AddCommGroup V] (κ₁ : GNode G₁.tree → V)
    (κ₂ : GNode G₂.tree → V) (z : Fin w × Path) : V := by
  classical
  exact if z.1 = 0 ∧ ¬ X.lonePath <+: z.2 then extend κ₁ ((0 : Fin 1), z.2)
    else extend κ₂ (unbot X.lonePath z)

/-- The glued function on the nodes of `G`. -/
noncomputable def glue {V : Type*} [AddCommGroup V] (κ₁ : GNode G₁.tree → V)
    (κ₂ : GNode G₂.tree → V) (z : GNode G.tree) : V :=
  glueAddr (X := X) κ₁ κ₂ z.1

/-- The splitting hypothesis on decorations (proved from the code for each instance). -/
def DecSplit (V : Type*) [AddCommGroup V] : Prop :=
  ∀ κ : GNode G.tree → V, IsDecoration G κ →
    IsDecoration G₁ (κ ∘ h.ι₁) ∧ IsDecoration G₂ (κ ∘ h.ι₂)

/-- The gluing hypothesis on decorations (proved from the code for each instance). -/
def DecGlue (V : Type*) [AddCommGroup V] : Prop :=
  ∀ (κ₁ : GNode G₁.tree → V) (κ₂ : GNode G₂.tree → V), IsDecoration G₁ κ₁ → IsDecoration G₂ κ₂ →
    κ₁ (GNode.root G₁.tree 0) = 0 → κ₂ (GNode.root G₂.tree 0) = 0 → IsDecoration G (glue (X := X) κ₁ κ₂)

theorem glue_ι₁ {V : Type*} [AddCommGroup V] (κ₁ : GNode G₁.tree → V) (κ₂ : GNode G₂.tree → V)
    (hκ₁ : IsDecoration G₁ κ₁) (h0 : κ₁ (GNode.root G₁.tree 0) = 0)
    (h0' : κ₂ (GNode.root G₂.tree 0) = 0) (x : GNode G₁.tree) : glue (X := X) κ₁ κ₂ (h.ι₁ x) = κ₁ x := by
  classical
  unfold glue glueAddr
  by_cases ht : X.lonePath <+: x.1.2
  · have hx : x = h.lone := by
      apply Subtype.ext
      obtain ⟨⟨j, p⟩, hp⟩ := x
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      have hp' : p ∈ (X.plug (G.sig 0) .leaf).nodes := by rw [← h.tree1]; exact hp
      simp only [lone, Prod.mk.injEq, true_and]
      exact plug_leaf_prefix X _ hp' ht
    subst hx
    have hc : ¬ ((h.ι₁ h.lone).1.1 = 0 ∧ ¬ X.lonePath <+: (h.ι₁ h.lone).1.2) := by
      show ¬ (((0 : Fin w), X.lonePath).1 = 0 ∧ ¬ X.lonePath <+: ((0 : Fin w), X.lonePath).2)
      simp
    rw [ite_eq_right hc, h.lone_eq_root hκ₁, h0]
    have : unbot X.lonePath (h.ι₁ h.lone).1 = (GNode.root G₂.tree 0).1 := by
      show unbot X.lonePath ((0 : Fin w), X.lonePath) = ((0 : Fin w), [])
      simp [unbot]
    rw [this, extend_node, h0']
  · have hc : (h.ι₁ x).1.1 = 0 ∧ ¬ X.lonePath <+: (h.ι₁ x).1.2 := ⟨rfl, ht⟩
    rw [ite_eq_left hc]
    have : ((0 : Fin 1), (h.ι₁ x).1.2) = x.1 := by
      obtain ⟨⟨j, p⟩, hp⟩ := x
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      rfl
    rw [this, extend_node]

theorem glue_ι₂ {V : Type*} [AddCommGroup V] (κ₁ : GNode G₁.tree → V) (κ₂ : GNode G₂.tree → V)
    (y : GNode G₂.tree) : glue (X := X) κ₁ κ₂ (h.ι₂ y) = κ₂ y := by
  classical
  unfold glue glueAddr
  have hc : ¬ ((h.ι₂ y).1.1 = 0 ∧ ¬ X.lonePath <+: (h.ι₂ y).1.2) := botAddr_not_top X.lonePath y.1
  rw [ite_eq_right hc]
  show extend κ₂ (unbot X.lonePath (botAddr X.lonePath y.1)) = κ₂ y
  rw [unbot_botAddr, extend_node]

theorem glue_restrict {V : Type*} [AddCommGroup V] (κ : GNode G.tree → V) :
    glue (X := X) (κ ∘ h.ι₁) (κ ∘ h.ι₂) = κ := by
  classical
  funext z
  unfold glue glueAddr
  by_cases ht : z.1.1 = 0 ∧ ¬ X.lonePath <+: z.1.2
  · rw [ite_eq_left ht]
    have hm : ((0 : Fin 1), z.1.2).2 ∈ (G₁.tree ((0 : Fin 1), z.1.2).1).nodes := by
      have hz := z.2
      rw [ht.1] at hz
      exact (h.top_node_iff _ ht.2).mpr hz
    unfold extend
    rw [dite_eq_left hm]
    show κ (h.ι₁ ⟨_, hm⟩) = κ z
    congr 1
    apply Subtype.ext
    obtain ⟨⟨j, p⟩, _⟩ := z
    simp only at ht
    obtain ⟨rfl, -⟩ := ht
    rfl
  · rw [ite_eq_right ht]
    have hb : botAddr X.lonePath (unbot X.lonePath z.1) = z.1 :=
      botAddr_unbot fun h0 => by
        by_contra hne
        exact ht ⟨h0, hne⟩
    have hm : (unbot X.lonePath z.1).2 ∈ (G₂.tree (unbot X.lonePath z.1).1).nodes := by
      have := (h.bot_iff (unbot X.lonePath z.1)).1
      rw [hb] at this
      exact this.mp z.2
    unfold extend
    rw [dite_eq_left hm]
    show κ (h.ι₂ ⟨_, hm⟩) = κ z
    congr 1
    exact Subtype.ext hb

/-- **Decorations of `G` with zero roots are pairs of decorations of the pieces.** -/
noncomputable def decEquiv {d : ℕ} (hs : h.DecSplit (Fin d → ℤ)) (hg : DecGlue (G := G) (G₁ := G₁) (G₂ := G₂) (X := X) (Fin d → ℤ))
    (hfl : ∀ ℓ : GLeaf G.tree, ¬ G.IsFlower ℓ) (hfl₁ : ∀ ℓ : GLeaf G₁.tree, ¬ G₁.IsFlower ℓ)
    (hfl₂ : ∀ ℓ : GLeaf G₂.tree, ¬ G₂.IsFlower ℓ) :
    GenDecoration G d (fun _ => 0) 0 ≃
      GenDecoration G₁ d (fun _ => 0) 0 × GenDecoration G₂ d (fun _ => 0) 0 where
  toFun κ :=
    have h1 : IsDecoration G₁ (κ.1 ∘ h.ι₁) := (hs κ.1 κ.2.1).1
    (⟨κ.1 ∘ h.ι₁, h1, fun j => by
        have hj : j = 0 := Subsingleton.elim _ _
        subst hj
        exact κ.2.2.1 0, fun ℓ hℓ => absurd hℓ (hfl₁ ℓ)⟩,
      ⟨κ.1 ∘ h.ι₂, (hs κ.1 κ.2.1).2, fun j => by
        by_cases hj : j = 0
        · subst hj
          show κ.1 (h.ι₂ (GNode.root G₂.tree 0)) = 0
          rw [← h.ι₁_lone]
          show (κ.1 ∘ h.ι₁) h.lone = 0
          rw [h.lone_eq_root h1]
          exact κ.2.2.1 0
        · show κ.1 (h.ι₂ (GNode.root G₂.tree j)) = 0
          rw [h.ι₂_root hj]
          exact κ.2.2.1 j, fun ℓ hℓ => absurd hℓ (hfl₂ ℓ)⟩)
  invFun κκ :=
    ⟨glue (X := X) κκ.1.1 κκ.2.1, hg _ _ κκ.1.2.1 κκ.2.2.1 (κκ.1.2.2.1 0) (κκ.2.2.2.1 0), fun j => by
        by_cases hj : j = 0
        · subst hj
          rw [← h.ι₁_root, h.glue_ι₁ _ _ κκ.1.2.1 (κκ.1.2.2.1 0) (κκ.2.2.2.1 0)]
          exact κκ.1.2.2.1 0
        · rw [← h.ι₂_root hj, h.glue_ι₂]
          exact κκ.2.2.2.1 j, fun ℓ hℓ => absurd hℓ (hfl ℓ)⟩
  left_inv κ := Subtype.ext (h.glue_restrict κ.1)
  right_inv κκ := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · funext x
      exact h.glue_ι₁ _ _ κκ.1.2.1 (κκ.1.2.2.1 0) (κκ.2.2.2.1 0) x
    · funext y
      exact h.glue_ι₂ _ _ y

end GlueData

end WaveTurbulence.PL234
