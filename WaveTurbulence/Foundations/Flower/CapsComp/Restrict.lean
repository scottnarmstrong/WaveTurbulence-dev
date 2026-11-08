/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsGlue.Garden
/-! # A3b CAPS-COMP: every garden whose blocks are pairing-closed is an n-ary glue, and the glue is injective

For `σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w`, a (layered) garden of width `w` in which the pairing maps each block
`{σ ⟨c, i⟩ | i}` into itself is the glue `CapsGlue.glueL σ` of its restrictions (`exists_glueL`), and the glue
is injective (`glueL_injective`). This is the n-ary analogue of FLOWER-P7's `GlueSurj` (binary). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsComp
open TTree Finset WaveTurbulence.FlowerP7 WaveTurbulence.Flower.CapsGlue

/-! ## Extensionality of gardens and layered gardens through addresses -/

theorem garden_ext' {n : ℕ} {G G' : Garden n} (hs : G.sig = G'.sig) (ht : G.tree = G'.tree)
    (hp : ∀ (ℓ : GLeaf G.tree) (ℓ' : GLeaf G'.tree), ℓ.1 = ℓ'.1 → (G.pair ℓ).1 = (G'.pair ℓ').1)
    (hm : ∀ (ℓ : GLeaf G.tree) (ℓ' : GLeaf G'.tree), ℓ.1 = ℓ'.1 → G.mark ℓ = G'.mark ℓ') : G = G' := by
  obtain ⟨s, t, p, mk, a1, a2, a3⟩ := G
  obtain ⟨s', t', p', mk', b1, b2, b3⟩ := G'
  simp only at hs ht hp hm
  subst hs ht
  have e1 : p = p' := funext fun ℓ => Subtype.ext (hp ℓ ℓ rfl)
  have e2 : mk = mk' := funext fun ℓ => hm ℓ ℓ rfl
  subst e1 e2
  rfl

theorem layered_ext' {n : ℕ} {LG LG' : LayeredGarden n} (hg : LG.garden = LG'.garden)
    (hl : ∀ (x : GNode LG.garden.tree) (x' : GNode LG'.garden.tree), x.1 = x'.1 → LG.layer x = LG'.layer x') :
    LG = LG' := by
  obtain ⟨G, l, h⟩ := LG
  obtain ⟨G', l', h'⟩ := LG'
  simp only at hg hl
  subst hg
  have e : l = l' := funext fun x => hl x x rfl
  subst e
  rfl

/-- Equal gardens have the same pairing on equal addresses. -/
theorem pair_val_eq_of_eq {n : ℕ} {G G' : Garden n} (h : G = G') (ℓ : GLeaf G.tree) (ℓ' : GLeaf G'.tree)
    (hl : ℓ.1 = ℓ'.1) : (G.pair ℓ).1 = (G'.pair ℓ').1 := by
  subst h
  rw [show ℓ = ℓ' from Subtype.ext hl]

theorem mark_eq_of_eq {n : ℕ} {G G' : Garden n} (h : G = G') (ℓ : GLeaf G.tree) (ℓ' : GLeaf G'.tree)
    (hl : ℓ.1 = ℓ'.1) : G.mark ℓ = G'.mark ℓ' := by
  subst h
  rw [show ℓ = ℓ' from Subtype.ext hl]

theorem layer_eq_of_eq {n : ℕ} {LG LG' : LayeredGarden n} (h : LG = LG') (x : GNode LG.garden.tree)
    (x' : GNode LG'.garden.tree) (hx : x.1 = x'.1) : LG.layer x = LG'.layer x' := by
  subst h
  rw [show x = x' from Subtype.ext hx]

variable {m w : ℕ} {a : Fin m → ℕ}

/-! ## Injectivity of the n-ary glue -/

theorem glueGardenN_injective (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) {GA GB : ∀ c, Garden (a c)}
    (h : glueGardenN σ GA = glueGardenN σ GB) : GA = GB := by
  funext c
  have ht : (GA c).tree = (GB c).tree := by
    funext i
    have := congrFun (congrArg Garden.tree h) (σ ⟨c, i⟩)
    simpa only [glueGardenN_tree, gT_apply] using this
  refine garden_ext' ?_ ht ?_ ?_
  · funext i
    have := congrFun (congrArg Garden.sig h) (σ ⟨c, i⟩)
    simp only [gSigN] at this
    rw [Equiv.symm_apply_apply] at this
    exact this
  · intro ℓ ℓ' hl
    have := pair_val_eq_of_eq h (glueLeafN σ (fun c => (GA c).tree) ⟨c, ℓ⟩)
      (glueLeafN σ (fun c => (GB c).tree) ⟨c, ℓ'⟩) (by simp [hl])
    rw [glueN_pair_leaf, glueN_pair_leaf, glueLeafN_val, glueLeafN_val] at this
    obtain ⟨e1, e2⟩ := Prod.mk.inj this
    have e3 := σ.injective e1
    rw [Sigma.mk.inj_iff] at e3
    exact Prod.ext (eq_of_heq e3.2) e2
  · intro ℓ ℓ' hl
    have := mark_eq_of_eq h (glueLeafN σ (fun c => (GA c).tree) ⟨c, ℓ⟩)
      (glueLeafN σ (fun c => (GB c).tree) ⟨c, ℓ'⟩) (by simp [hl])
    rwa [glueN_mark_leaf, glueN_mark_leaf] at this

theorem glueL_injective (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) {LA LB : ∀ c, LayeredGarden (a c)}
    (h : glueL σ LA = glueL σ LB) : LA = LB := by
  have hg : (fun c => (LA c).garden) = fun c => (LB c).garden :=
    glueGardenN_injective σ (congrArg LayeredGarden.garden h)
  funext c
  refine layered_ext' (congrFun hg c) fun x x' hx => ?_
  have := layer_eq_of_eq h (glueNodeN σ (fun c => (LA c).garden.tree) ⟨c, x⟩)
    (glueNodeN σ (fun c => (LB c).garden.tree) ⟨c, x'⟩) (by simp [hx])
  rwa [glueL_layer, glueL_layer] at this

/-! ## Existence of the decomposition -/

theorem gT_restrictN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (T : Fin w → TTree) :
    CapsGlue.gT σ (fun c i => T (σ ⟨c, i⟩)) = T := by
  funext x
  show T (σ (σ.symm x)) = T x
  rw [Equiv.apply_symm_apply]

/-- **Existence of the split.** A garden in which every block `{σ ⟨c, ·⟩}` is closed under the pairing is the
glue of its restrictions. -/
theorem exists_glueGardenN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (G : Garden w)
    (hcl : ∀ (ℓ : GLeaf G.tree) (c : Fin m) (i : Fin (a c)), ℓ.1.1 = σ ⟨c, i⟩ →
      ∃ i' : Fin (a c), (G.pair ℓ).1.1 = σ ⟨c, i'⟩) :
    ∃ GA : ∀ c, Garden (a c), glueGardenN σ GA = G := by
  obtain ⟨sg, tr, pr, mk, h1, h2, h3⟩ := G
  simp only at hcl
  have htr := gT_restrictN σ tr
  generalize hTA : (fun c i => tr (σ ⟨c, i⟩)) = TA at htr
  subst htr
  have hA : ∀ (c : Fin m) (x : GLeaf (TA c)), ∃ y : GLeaf (TA c),
      pr (glueLeafN σ TA ⟨c, x⟩) = glueLeafN σ TA ⟨c, y⟩ := by
    intro c x
    obtain ⟨i', hi'⟩ := hcl (glueLeafN σ TA ⟨c, x⟩) c x.1.1 rfl
    obtain ⟨⟨c', y⟩, hz⟩ := (glueLeafN σ TA).surjective (pr (glueLeafN σ TA ⟨c, x⟩))
    rw [← hz, glueLeafN_val] at hi'
    have e := σ.injective hi'
    simp only [Sigma.mk.inj_iff] at e
    obtain ⟨rfl, -⟩ := e
    exact ⟨y, hz.symm⟩
  choose pA hpA using hA
  let GA : ∀ c, Garden (a c) := fun c =>
    { sig := fun i => sg (σ ⟨c, i⟩), tree := TA c, pair := pA c,
      mark := fun x => mk (glueLeafN σ TA ⟨c, x⟩)
      pair_pair := fun x => by
        apply ((glueLeafN σ TA).injective.comp sigma_mk_injective).eq_iff.mp
        show glueLeafN σ TA ⟨c, pA c (pA c x)⟩ = glueLeafN σ TA ⟨c, x⟩
        rw [← hpA, ← hpA, h1]
      pair_eq_iff := fun x => by
        have := h2 (glueLeafN σ TA ⟨c, x⟩)
        rw [hpA] at this
        simpa only [EmbeddingLike.apply_eq_iff_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and] using this
      pair_sign := fun x hx => by
        have hne : pr (glueLeafN σ TA ⟨c, x⟩) ≠ glueLeafN σ TA ⟨c, x⟩ := by
          rw [hpA]
          intro e
          exact hx (by simpa using e)
        have := h3 _ hne
        rw [hpA] at this
        exact this }
  refine ⟨GA, garden_ext' ?_ rfl ?_ ?_⟩
  · funext x
    show sg (σ ⟨(σ.symm x).1, (σ.symm x).2⟩) = sg x
    rw [show (⟨(σ.symm x).1, (σ.symm x).2⟩ : Σ c, Fin (a c)) = σ.symm x from rfl, Equiv.apply_symm_apply]
  · intro ℓ ℓ' hl
    rw [show ℓ' = ℓ from Subtype.ext hl.symm]
    obtain ⟨⟨c, x⟩, rfl⟩ := (glueLeafN σ TA).surjective ℓ
    exact (congrArg Subtype.val (glueN_pair_leaf σ GA c x)).trans (congrArg Subtype.val (hpA c x).symm)
  · intro ℓ ℓ' hl
    rw [show ℓ' = ℓ from Subtype.ext hl.symm]
    obtain ⟨⟨c, x⟩, rfl⟩ := (glueLeafN σ TA).surjective ℓ
    exact glueN_mark_leaf σ GA c x

/-- Layered version of `exists_glueGardenN`. -/
theorem exists_glueL (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LG : LayeredGarden w)
    (hcl : ∀ (ℓ : GLeaf LG.garden.tree) (c : Fin m) (i : Fin (a c)), ℓ.1.1 = σ ⟨c, i⟩ →
      ∃ i' : Fin (a c), (LG.garden.pair ℓ).1.1 = σ ⟨c, i'⟩) :
    ∃ LA : ∀ c, LayeredGarden (a c), glueL σ LA = LG := by
  obtain ⟨GA, hG⟩ := exists_glueGardenN σ LG.garden hcl
  obtain ⟨G, layer, hl⟩ := LG
  simp only at hG
  subst hG
  refine ⟨fun c => ⟨GA c, fun x => layer (glueNodeN σ (fun c => (GA c).tree) ⟨c, x⟩), ?_⟩, ?_⟩
  · constructor
    · intro br i
      have h := hl.1 (glueBranchN σ (fun c => (GA c).tree) ⟨c, br⟩) i
      rwa [glueBranchN_child, glueBranchN_toNode] at h
    · intro ℓ
      have h := hl.2 (glueLeafN σ (fun c => (GA c).tree) ⟨c, ℓ⟩)
      rwa [glueN_pair_leaf, glueLeafN_toNode, glueLeafN_toNode] at h
  · refine layered_ext' rfl fun x x' hx => ?_
    rw [show x' = x from Subtype.ext hx.symm]
    obtain ⟨⟨c, y⟩, rfl⟩ := (glueNodeN σ fun c => (GA c).tree).surjective x
    exact gLayerN_apply σ GA (fun c x => layer (glueNodeN σ (fun c => (GA c).tree) ⟨c, x⟩)) c y

end WaveTurbulence.Flower.CapsComp
