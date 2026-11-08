/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsId.Inject
/-! # A3b CAPS-COMP: the uncapping inverse (supplement Lemma 2.1(3)–(4), surjectivity of capping)

A garden of width `2w` has the **cap shape** (`CapShape`) if it is plain, the trees `capσ w (inr j)` (the caps) are
trivial, and the leaf of the cap of tree `j` is paired into tree `capσ w (inl j)`. Every such layered garden is the
capped garden of a garden of width `w` with exactly one flower per tree (`exists_uncap`): the flower of tree `j` is
the leaf paired with the cap of tree `j`. With `CapsId.capLayered_injective` this is the bijection of Lemma 2.1. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsComp
open TTree Finset WaveTurbulence.FlowerP7 WaveTurbulence.Flower.CapsId

variable {w : ℕ}

/-- The cap shape of a garden of width `2w`. -/
structure CapShape (G : Garden (2 * w)) : Prop where
  plain : G.IsPlain
  capLeaf : ∀ j, G.tree (capσ w (.inr j)) = TTree.leaf
  capPair : ∀ ℓ : GLeaf G.tree, ∀ j, ℓ.1.1 = capσ w (.inr j) → (G.pair ℓ).1.1 = capσ w (.inl j)

/-- The capped garden of a garden with one flower per tree has the cap shape. -/
theorem capShape_capGarden (G : Garden w) (hF : OneFlower G) (hm : ∀ ℓ, G.mark ℓ ≠ none → G.IsFlower ℓ) :
    CapShape (capGarden G) := by
  refine ⟨?_, fun j => capGarden_tree_inr G j, ?_⟩
  · intro x
    rcases leaf_cases G x with ⟨ℓ, rfl⟩ | ⟨j, rfl⟩
    · by_cases hℓ : G.IsFlower ℓ
      · exact capGarden_mark_flower G hF hℓ
      · rw [capGarden_mark_nonflower G hF hℓ]
        by_contra h
        exact hℓ (hm ℓ h)
    · exact capGarden_mark_capL_of G hF j
  · intro x j hx
    rcases leaf_cases G x with ⟨ℓ, rfl⟩ | ⟨j', rfl⟩
    · exfalso
      have : capσ w (.inl ℓ.1.1) = capσ w (.inr j) := hx
      exact Sum.inl_ne_inr ((capσ w).injective this)
    · have hj : j' = j := Sum.inr_injective ((capσ w).injective hx)
      subst hj
      obtain ⟨ℓ, hℓ⟩ := flowerOf_isSome hF j'
      rw [capGarden_pair_capL_of G hℓ]
      show capσ w (.inl ℓ.1.1) = _
      rw [(flowerOf_spec hℓ).1]

section Uncap

variable (TA : Fin w → TTree)

/-- The partner of an original leaf, read on `original leaves ⊕ cap leaves`. -/
def partnerS (pr : GLeaf (capTree TA) → GLeaf (capTree TA)) (ℓ : GLeaf TA) : GLeaf TA ⊕ GLeaf (capForest w) :=
  (glueLeaf (capσ w) TA (capForest w)).symm (pr (glueLeaf (capσ w) TA (capForest w) (.inl ℓ)))

theorem partnerS_spec (pr : GLeaf (capTree TA) → GLeaf (capTree TA)) (ℓ : GLeaf TA) :
    glueLeaf (capσ w) TA (capForest w) (partnerS TA pr ℓ) = pr (glueLeaf (capσ w) TA (capForest w) (.inl ℓ)) := by
  unfold partnerS; rw [Equiv.apply_symm_apply]

/-- The uncapped pairing. -/
def uncapPair (pr : GLeaf (capTree TA) → GLeaf (capTree TA)) (ℓ : GLeaf TA) : GLeaf TA :=
  Sum.elim id (fun _ => ℓ) (partnerS TA pr ℓ)

/-- The uncapped marks: the leaves paired with a cap are flowers. -/
def uncapMark (pr : GLeaf (capTree TA) → GLeaf (capTree TA)) (ℓ : GLeaf TA) : Option MarkTag :=
  Sum.elim (fun _ => none) (fun _ => some MarkTag.equal) (partnerS TA pr ℓ)

end Uncap

/-- The garden recovered from the raw fields of a capped garden written on the cap forest `capTree TA`. -/
@[reducible] def uncapGarden (TA : Fin w → TTree) (sg : Fin (2 * w) → ℤˣ) (pr : GLeaf (capTree TA) → GLeaf (capTree TA))
    (h1 : ∀ ℓ, pr (pr ℓ) = ℓ) (hfix : ∀ ℓ, pr ℓ ≠ ℓ)
    (h3 : ∀ ℓ, pr ℓ ≠ ℓ → nodeSign sg (pr ℓ).1 = -nodeSign sg ℓ.1) : Garden w where
  sig := fun j => sg (capσ w (.inl j))
  tree := TA
  pair := uncapPair TA pr
  mark := uncapMark TA pr
  pair_pair := fun ℓ => by
    unfold uncapPair
    rcases hs : partnerS TA pr ℓ with ℓ' | c
    · simp only [Sum.elim_inl, id]
      have e1 := partnerS_spec TA pr ℓ
      rw [hs] at e1
      have e2 : partnerS TA pr ℓ' = .inl ℓ := by
        unfold partnerS
        rw [e1, h1, Equiv.symm_apply_apply]
      rw [e2]; rfl
    · simp only [Sum.elim_inr, hs]
  pair_eq_iff := fun ℓ => by
    unfold uncapPair uncapMark
    rcases hs : partnerS TA pr ℓ with ℓ' | c
    · simp only [Sum.elim_inl, id, ne_eq, not_true_eq_false, iff_false]
      intro he
      subst he
      have e1 := partnerS_spec TA pr ℓ'
      rw [hs] at e1
      exact hfix _ e1.symm
    · simp
  pair_sign := fun ℓ hℓ => by
    unfold uncapPair at hℓ ⊢
    rcases hs : partnerS TA pr ℓ with ℓ' | c
    · rw [hs] at hℓ
      simp only [Sum.elim_inl, id] at hℓ ⊢
      have e1 := partnerS_spec TA pr ℓ
      rw [hs] at e1
      have := h3 (glueLeaf (capσ w) TA (capForest w) (.inl ℓ)) (hfix _)
      rw [← e1] at this
      exact this
    · rw [hs] at hℓ
      exact absurd rfl hℓ

section Raw

variable (TA : Fin w → TTree) (pr : GLeaf (capTree TA) → GLeaf (capTree TA))

/-- The glued leaf of the cap of tree `j`. -/
abbrev capGL (j : Fin w) : GLeaf (capTree TA) := glueLeaf (capσ w) TA (capForest w) (.inr (capLeafF j))

/-- The original leaf paired with the cap of tree `j`. -/
theorem exists_capPartner (hcp : ∀ ℓ : GLeaf (capTree TA), ∀ j, ℓ.1.1 = capσ w (.inr j) →
      (pr ℓ).1.1 = capσ w (.inl j)) (j : Fin w) :
    ∃ ℓ : GLeaf TA, ℓ.1.1 = j ∧ pr (capGL TA j) = glueLeaf (capσ w) TA (capForest w) (.inl ℓ) := by
  have hj := hcp (capGL TA j) j rfl
  obtain ⟨z, hz⟩ := (glueLeaf (capσ w) TA (capForest w)).surjective (pr (capGL TA j))
  rcases z with ℓ | c
  · refine ⟨ℓ, ?_, hz.symm⟩
    rw [← hz] at hj
    exact Sum.inl_injective ((capσ w).injective hj)
  · rw [← hz] at hj
    exact absurd ((capσ w).injective hj) (by simp)

theorem partnerS_eq_inr_iff (h1 : ∀ ℓ, pr (pr ℓ) = ℓ) (hcp : ∀ ℓ : GLeaf (capTree TA), ∀ j, ℓ.1.1 = capσ w (.inr j) →
      (pr ℓ).1.1 = capσ w (.inl j)) (ℓ : GLeaf TA) (c : GLeaf (capForest w)) :
    partnerS TA pr ℓ = .inr c ↔ c = capLeafF ℓ.1.1 ∧ pr (capGL TA ℓ.1.1) = glueLeaf (capσ w) TA (capForest w) (.inl ℓ) := by
  constructor
  · intro hs
    obtain ⟨j, rfl⟩ : ∃ j, c = capLeafF j := ⟨c.1.1, capLeafF_eq c⟩
    have e1 := partnerS_spec TA pr ℓ
    rw [hs] at e1
    have e2 : pr (capGL TA j) = glueLeaf (capσ w) TA (capForest w) (.inl ℓ) := by
      rw [show capGL TA j = glueLeaf (capσ w) TA (capForest w) (.inr (capLeafF j)) from rfl, e1, h1]
    obtain ⟨ℓ', hℓ', e3⟩ := exists_capPartner TA pr hcp j
    rw [e3] at e2
    have hℓℓ' : ℓ' = ℓ := Sum.inl_injective ((glueLeaf (capσ w) TA (capForest w)).injective e2)
    subst hℓℓ'
    subst hℓ'
    exact ⟨rfl, e3⟩
  · rintro ⟨rfl, h⟩
    unfold partnerS
    rw [← h, h1, Equiv.symm_apply_apply]

/-- The raw uncapped layering. -/
def uncapLayer (lay : GNode (capTree TA) → ℕ) : GNode TA → ℕ :=
  fun x => lay (glueNode (capσ w) TA (capForest w) (.inl x))

theorem uncapLayer_isLayering (sg : Fin (2 * w) → ℤˣ) (h1 : ∀ ℓ, pr (pr ℓ) = ℓ) (hfix : ∀ ℓ, pr ℓ ≠ ℓ)
    (h3 : ∀ ℓ, pr ℓ ≠ ℓ → nodeSign sg (pr ℓ).1 = -nodeSign sg ℓ.1) (lay : GNode (capTree TA) → ℕ)
    (hl1 : ∀ (b : GBranch (capTree TA)) (i : Fin 3), lay (b.child i) ≤ lay b.toNode)
    (hl2 : ∀ ℓ : GLeaf (capTree TA), lay ℓ.toNode = lay (pr ℓ).toNode) :
    IsLayering (uncapGarden TA sg pr h1 hfix h3) (uncapLayer TA lay) := by
  constructor
  · intro b i
    have := hl1 (glueBranch (capσ w) TA (capForest w) (.inl b)) i
    rwa [glueBranch_child_inl, glueBranch_toNode_inl] at this
  · intro ℓ
    show uncapLayer TA lay ℓ.toNode = uncapLayer TA lay (uncapPair TA pr ℓ).toNode
    unfold uncapPair
    rcases hs : partnerS TA pr ℓ with ℓ' | c
    · have e1 := partnerS_spec TA pr ℓ
      rw [hs] at e1
      have := hl2 (glueLeaf (capσ w) TA (capForest w) (.inl ℓ))
      rw [← e1, glueLeaf_toNode_inl, glueLeaf_toNode_inl] at this
      exact this
    · rfl

end Raw

/-- **The uncapping inverse** (supplement Lemma 2.1(3)–(4)): every layered garden of cap shape is the capped
garden of a garden of width `w` with exactly one flower per tree, all of whose marked leaves are flowers, with the
original signs. -/
theorem exists_uncap (LG' : LayeredGarden (2 * w)) (p : ℕ) (hG : CapShape LG'.garden) :
    ∃ LG : LayeredGarden w, OneFlower LG.garden ∧ (∀ ℓ, LG.garden.mark ℓ ≠ none → LG.garden.IsFlower ℓ) ∧
      (∀ j, LG.garden.sig j = LG'.garden.sig (capσ w (.inl j))) ∧ capLayered LG p = LG' := by
  obtain ⟨⟨sg, tr, pr, mk, h1, h2, h3⟩, lay, hl⟩ := LG'
  obtain ⟨hpl, hcl, hcp⟩ := hG
  have htr : capTree (fun j => tr (capσ w (.inl j))) = tr := by
    funext c
    obtain ⟨s, rfl⟩ := (capσ w).surjective c
    rcases s with j | j
    · simp
    · simp only [gT_inr]
      exact (hcl j).symm
  generalize hTA : (fun j => tr (capσ w (.inl j))) = TA at htr
  subst htr
  have hmk : ∀ ℓ, mk ℓ = none := hpl
  have hfix : ∀ ℓ, pr ℓ ≠ ℓ := fun ℓ e => (h2 ℓ).1 e (hmk ℓ)
  have hcp' : ∀ ℓ : GLeaf (capTree TA), ∀ j, ℓ.1.1 = capσ w (.inr j) → (pr ℓ).1.1 = capσ w (.inl j) := hcp
  set G0 := uncapGarden TA sg pr h1 hfix h3 with hG0
  have hfl : ∀ ℓ : GLeaf TA, G0.IsFlower ℓ ↔ ∃ c, partnerS TA pr ℓ = .inr c := by
    intro ℓ
    show uncapMark TA pr ℓ = some MarkTag.equal ↔ _
    unfold uncapMark
    rcases partnerS TA pr ℓ with ℓ' | c <;> simp
  have hflj : ∀ ℓ : GLeaf TA, G0.IsFlower ℓ ↔
      pr (capGL TA ℓ.1.1) = glueLeaf (capσ w) TA (capForest w) (.inl ℓ) := by
    intro ℓ
    rw [hfl]
    constructor
    · rintro ⟨c, hc⟩
      exact ((partnerS_eq_inr_iff TA pr h1 hcp' ℓ c).1 hc).2
    · intro h
      exact ⟨_, (partnerS_eq_inr_iff TA pr h1 hcp' ℓ _).2 ⟨rfl, h⟩⟩
  have hF : OneFlower G0 := by
    intro j
    obtain ⟨ℓ, hℓj, hℓ⟩ := exists_capPartner TA pr hcp' j
    refine ⟨ℓ, ⟨hℓj, (hflj ℓ).2 (by rw [hℓj]; exact hℓ)⟩, fun ℓ' ⟨hj', hf'⟩ => ?_⟩
    have e := (hflj ℓ').1 hf'
    rw [hj', hℓ] at e
    exact (Sum.inl_injective ((glueLeaf (capσ w) TA (capForest w)).injective e)).symm
  have hflowerOf : ∀ j, ∃ ℓ, flowerOf G0 j = some ℓ ∧ ℓ.1.1 = j ∧
      pr (capGL TA j) = glueLeaf (capσ w) TA (capForest w) (.inl ℓ) := by
    intro j
    obtain ⟨ℓ, hℓ⟩ := flowerOf_isSome hF j
    obtain ⟨hj, hf⟩ := flowerOf_spec hℓ
    refine ⟨ℓ, hℓ, hj, ?_⟩
    have := (hflj ℓ).1 hf
    rwa [hj] at this
  let LG0 : LayeredGarden w := ⟨G0, uncapLayer TA lay, uncapLayer_isLayering TA pr sg h1 hfix h3 lay hl.1 hl.2⟩
  refine ⟨LG0, hF, ?_, fun j => rfl, ?_⟩
  · intro ℓ hm
    show uncapMark TA pr ℓ = some MarkTag.equal
    revert hm
    show uncapMark TA pr ℓ ≠ none → _
    unfold uncapMark
    rcases partnerS TA pr ℓ with ℓ' | c <;> simp
  -- the capped garden of `LG0` is the given garden
  have hsig : capSig G0 = sg := by
    funext c
    obtain ⟨s, rfl⟩ := (capσ w).surjective c
    rcases s with j | j
    · exact capGarden_sig_inl G0 j
    · rw [show capSig G0 (capσ w (.inr j)) = capSigCaps G0 j from capGarden_sig_inr G0 j]
      obtain ⟨ℓ, hℓ, hj, hpr⟩ := hflowerOf j
      unfold capSigCaps
      rw [hℓ]
      show -nodeSign G0.sig ℓ.1 = _
      have e := h3 (capGL TA j) (hfix _)
      rw [hpr] at e
      have e2 : nodeSign sg (glueLeaf (capσ w) TA (capForest w) (.inl ℓ)).1 = nodeSign G0.sig ℓ.1 := rfl
      rw [e2] at e
      rw [e]
      simp [nodeSign, TTree.pathSign, capLeafF, hj]
  have hpair : ∀ x : GLeaf (capTree TA), (capGarden G0).pair x = pr x := by
    intro x
    obtain ⟨z, rfl⟩ := (glueLeaf (capσ w) TA (capForest w)).surjective x
    rcases z with ℓ | c
    · show (capGarden G0).pair (embL G0 ℓ) = _
      rw [capGarden_pair_embL]
      by_cases hc : flowerOf G0 ℓ.1.1 = some ℓ
      · rw [ite_eq_left hc]
        have hf := (flowerOf_self_iff hF ℓ).1 hc
        show capGL TA ℓ.1.1 = pr (glueLeaf (capσ w) TA (capForest w) (.inl ℓ))
        rw [← (hflj ℓ).1 hf, h1]
      · rw [ite_eq_right hc]
        have hf : ¬ G0.IsFlower ℓ := fun h => hc ((flowerOf_self_iff hF ℓ).2 h)
        rw [hfl] at hf
        rcases hs : partnerS TA pr ℓ with ℓ' | c
        · have e1 := partnerS_spec TA pr ℓ
          rw [hs] at e1
          show glueLeaf (capσ w) TA (capForest w) (.inl (uncapPair TA pr ℓ)) = _
          unfold uncapPair
          rw [hs]
          exact e1
        · exact absurd ⟨c, hs⟩ hf
    · obtain ⟨j, rfl⟩ : ∃ j, c = capLeafF j := ⟨c.1.1, capLeafF_eq c⟩
      show (capGarden G0).pair (capL G0 j) = _
      obtain ⟨ℓ, hℓ, -, hpr⟩ := hflowerOf j
      rw [capGarden_pair_capL_of G0 hℓ]
      exact hpr.symm
  have hmark : ∀ x : GLeaf (capTree TA), (capGarden G0).mark x = mk x := by
    intro x
    refine Eq.trans ?_ (hmk x).symm
    obtain ⟨z, rfl⟩ := (glueLeaf (capσ w) TA (capForest w)).surjective x
    rcases z with ℓ | c
    · show (capGarden G0).mark (embL G0 ℓ) = _
      by_cases hf : G0.IsFlower ℓ
      · exact capGarden_mark_flower G0 hF hf
      · rw [capGarden_mark_nonflower G0 hF hf]
        show uncapMark TA pr ℓ = none
        rw [hfl] at hf
        unfold uncapMark
        rcases hs : partnerS TA pr ℓ with ℓ' | c
        · rfl
        · exact absurd ⟨c, hs⟩ hf
    · obtain ⟨j, rfl⟩ : ∃ j, c = capLeafF j := ⟨c.1.1, capLeafF_eq c⟩
      exact capGarden_mark_capL_of G0 hF j
  have hgar : capGarden G0 = ⟨sg, capTree TA, pr, mk, h1, h2, h3⟩ := by
    unfold capGarden
    rw [Garden.mk.injEq]
    exact ⟨hsig, rfl, heq_of_eq (funext hpair), heq_of_eq (funext hmark)⟩
  show (⟨capGarden G0, capLayer LG0 p, _⟩ : LayeredGarden (2 * w)) = ⟨⟨sg, capTree TA, pr, mk, h1, h2, h3⟩, lay, hl⟩
  rw [LayeredGarden.mk.injEq]
  refine ⟨hgar, heq_of_eq (funext fun x => ?_)⟩
  obtain ⟨z, rfl⟩ := (glueNode (capσ w) TA (capForest w)).surjective x
  rcases z with a | c
  · exact capLayer_embN LG0 p a
  · obtain ⟨j, rfl⟩ : ∃ j, c = capNodeF j := ⟨c.1.1, capNodeF_eq c⟩
    show capLayer LG0 p (capN G0 j) = _
    rw [capLayer_capN]
    obtain ⟨ℓ, hℓ, -, hpr⟩ := hflowerOf j
    rw [hℓ]
    show lay (glueNode (capσ w) TA (capForest w) (.inl ℓ.toNode)) = _
    have := hl.2 (capGL TA j)
    change lay _ = lay (pr (capGL TA j)).toNode at this
    rw [hpr] at this
    exact this.symm

end WaveTurbulence.Flower.CapsComp
