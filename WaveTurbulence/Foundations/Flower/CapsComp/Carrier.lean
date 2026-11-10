/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsComp.Labels
public import WaveTurbulence.Foundations.Flower.CapsComp.Uncap
public import WaveTurbulence.Foundations.FC23.FlowerSlices
public import WaveTurbulence.Foundations.Molecule.LFTwist.TruncationScale
public import WaveTurbulence.Foundations.WaveB.Lemmas
/-! # A3b CAPS-COMP: the flower carrier read on the capped garden (supplement Lemma 2.1(2), (4))

* `canonCriterion_capLayered_iff`: with the flowers in layer `p`, the canonicity criterion of the capped garden is
  the criterion of the flower garden (Lemma 2.1(2): the only new completely paired configurations involve a cap,
  whose parent layer is read as `p`).
* `CapGlob`: the conditions of `FC23.flowerCarrier` written on the capped garden (criterion, order, signs, and per
  original tree: stem layer, kind, pattern). `mem_carrier_iff`: a garden is in the carrier iff it is a garden with
  one flower per tree and its capped garden satisfies `CapGlob`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsComp
open TTree Finset WaveTurbulence.FlowerP7 WaveTurbulence.Flower.CapsGlue WaveTurbulence.Flower.CapsId
open WaveTurbulence.Flower.MkDefs

variable {w : ℕ}

/-! ## Lemma 2.1(2): the criterion of the capped garden -/

theorem leavesBelow_embN (G : Garden w) (a : GNode G.tree) :
    (embN G a).leavesBelow = a.leavesBelow.image (embL G) := by
  ext x
  simp only [GNode.leavesBelow, mem_filter, mem_univ, true_and, mem_image]
  rcases leaf_cases G x with ⟨ℓ, rfl⟩ | ⟨j, rfl⟩
  · rw [embL_toNode, isDesc_embN]
    constructor
    · intro h; exact ⟨ℓ, h, rfl⟩
    · rintro ⟨ℓ', h, e⟩; rwa [← embL_injective G e]
  · constructor
    · rintro ⟨h, -⟩
      exact absurd ((capσ w).injective h) (by simp)
    · rintro ⟨ℓ', -, e⟩
      exact absurd e (embL_ne_capL G ℓ' j)

theorem completelyPaired_image_embL (G : Garden w) (hF : OneFlower G) (S : Finset (GLeaf G.tree)) :
    (capGarden G).CompletelyPaired (S.image (embL G)) ↔ G.CompletelyPaired S := by
  constructor
  · intro h ℓ hℓ
    obtain ⟨h1, h2⟩ := h (embL G ℓ) (mem_image_of_mem _ hℓ)
    obtain ⟨ℓ', hℓ', e⟩ := mem_image.1 h2
    by_cases hfl : G.IsFlower ℓ
    · rw [capGarden_pair_flower G hF hfl] at e
      exact absurd e (embL_ne_capL G ℓ' _)
    · rw [capGarden_pair_nonflower G hF hfl] at e h1
      refine ⟨fun hp => h1 (by rw [hp]), ?_⟩
      rwa [← embL_injective G e]
  · intro h x hx
    obtain ⟨ℓ, hℓ, rfl⟩ := mem_image.1 hx
    obtain ⟨h1, h2⟩ := h ℓ hℓ
    have hfl : ¬ G.IsFlower ℓ := by
      intro hf
      apply h1
      exact (G.pair_eq_iff ℓ).2 (by unfold Garden.IsFlower at hf; rw [hf]; exact Option.some_ne_none _)
    rw [capGarden_pair_nonflower G hF hfl]
    exact ⟨fun e => h1 (embL_injective G e), mem_image_of_mem _ h2⟩

theorem incomparable_embN (G : Garden w) (a a' : GNode G.tree) :
    (embN G a).Incomparable (embN G a') ↔ a.Incomparable a' := by
  unfold GNode.Incomparable
  rw [isDesc_embN, isDesc_embN]

theorem parentLayer_capN (LG : LayeredGarden w) (p top : ℕ) (j : Fin w) :
    (capLayered LG p).parentLayer top (capN LG.garden j) = top := by
  unfold LayeredGarden.parentLayer
  simp

/-- **Lemma 2.1(2), canonicity.** With the flowers in layer `p`, the capped garden satisfies the criterion iff
the flower garden does. -/
theorem canonCriterion_capLayered_iff (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden)
    (hfl : ∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ → LG.layer ℓ.toNode = p) :
    (capLayered LG p).CanonCriterion p ↔ LG.CanonCriterion p := by
  unfold LayeredGarden.CanonCriterion
  constructor
  · rintro ⟨hl, h⟩
    refine ⟨fun a => by have := hl (embN LG.garden a); rwa [capLayered_layer_embN] at this,
      fun a a' hinc hcp => ?_⟩
    have := h (embN LG.garden a) (embN LG.garden a') ((incomparable_embN _ a a').2 hinc) (by
      rw [leavesBelow_embN, leavesBelow_embN, ← image_union]
      exact (completelyPaired_image_embL LG.garden hF _).2 hcp)
    rwa [parentLayer_embN, parentLayer_embN, capLayered_layer_embN, capLayered_layer_embN] at this
  · rintro ⟨hl, h⟩
    have hcap : ∀ j, (capLayered LG p).layer (capN LG.garden j) = p :=
      capLayered_layer_capN_of LG p hfl
    refine ⟨fun x => ?_, fun x x' hinc hcp => ?_⟩
    · rcases node_cases LG.garden x with ⟨a, rfl⟩ | ⟨j, rfl⟩
      · rw [capLayered_layer_embN]; exact hl a
      · rw [hcap]
    · rcases node_cases LG.garden x with ⟨a, rfl⟩ | ⟨j, rfl⟩ <;>
        rcases node_cases LG.garden x' with ⟨a', rfl⟩ | ⟨j', rfl⟩
      · have := h a a' ((incomparable_embN _ a a').1 hinc) (by
          rw [leavesBelow_embN, leavesBelow_embN, ← image_union] at hcp
          exact (completelyPaired_image_embL LG.garden hF _).1 hcp)
        rwa [parentLayer_embN, parentLayer_embN, capLayered_layer_embN, capLayered_layer_embN]
      · rw [parentLayer_capN, hcap]
        exact (min_le_right _ _).trans (le_max_right _ _)
      · rw [parentLayer_capN, hcap]
        exact (min_le_left _ _).trans (le_max_left _ _)
      · rw [parentLayer_capN, parentLayer_capN, hcap, hcap]
        simp

/-! ## The flower carrier read on the capped garden -/

/-- The flower carrier's conditions on the capped garden (width `2w`, caps `capJ w`). -/
def CapGlob (P : WTParams) (p N : ℕ) (kind : FlowerKind) (pat : Fin w → FixPat) (ζ : ℤˣ)
    (G : LayeredGarden (2 * w)) : Prop :=
  G.CanonCriterion p ∧ G.garden.order = N ∧
    (∀ j : Fin w, G.garden.sig (capσ w (.inl j)) = (-1) ^ (j : ℕ)) ∧
    (∀ j : Fin w, G.garden.sig (capσ w (.inr j)) = -(ζ * (-1) ^ (j : ℕ))) ∧
    ∀ j : Fin w, CapStem G (capJ w) p (capσ w (.inl j)) ∧
      CapKindOK G (capJ w) p (P.N (p + 1)) (capσ w (.inl j)) kind ∧
      CapPatExist G (capJ w) p (capσ w (.inl j)) (pat j)

/-- `N_{p+1}^4 ≤ N_p` (also for `d = 0`, where both sides are `1`). -/
theorem N_fourth_le_N (P : WTParams) {p : ℕ} (hp : p < P.D) : P.N (p + 1) ^ 4 ≤ P.N p := by
  rcases Nat.eq_zero_or_pos P.d with hd | hd
  · simp [WTParams.N, hd]
  · exact LFTwist.N_fourth_le_pred P (q := p + 1) (by omega) (by omega) hd

theorem isFlowerGarden_of (G : Garden w) (hF : OneFlower G) (hm : ∀ ℓ, G.mark ℓ ≠ none → G.IsFlower ℓ)
    (hsig : ∀ j : Fin w, G.sig j = (-1) ^ (j : ℕ)) : G.IsFlowerGarden := by
  refine ⟨fun j => ?_, hm, hsig⟩
  obtain ⟨ℓ, ⟨hj, hf⟩, hu⟩ := hF j
  rw [Finset.card_eq_one]
  refine ⟨ℓ, ?_⟩
  ext x
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨hx, hmx⟩
    exact hu x ⟨hx, hm x hmx⟩
  · rintro rfl
    refine ⟨hj, ?_⟩
    unfold Garden.IsFlower at hf
    rw [hf]; exact Option.some_ne_none _

/-- **The carrier on the capped garden** (forward). -/
theorem capGlob_of_mem_carrier (P : WTParams) (p N : ℕ) (kind : FlowerKind) (pat : Fin w → FixPat) (ζ : ℤˣ)
    {LG : LayeredGarden w} (hLG : LG ∈ FC23.flowerCarrier P p N kind pat ζ) :
    OneFlower LG.garden ∧ (∀ ℓ, LG.garden.mark ℓ ≠ none → LG.garden.IsFlower ℓ) ∧
      CapShape (capLayered LG p).garden ∧ CapGlob P p N kind pat ζ (capLayered LG p) := by
  obtain ⟨⟨hfg, hstem, hcrit⟩, -, hord, hkind, hsgn, hpat⟩ := hLG
  have hF := oneFlower_of_isFlowerGarden hfg
  have hfl : ∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ → LG.layer ℓ.toNode = p :=
    fun ℓ hℓ => hstem _ ⟨ℓ, hℓ, GNode.isDesc_refl _⟩
  refine ⟨hF, hfg.2.1, capShape_capGarden LG.garden hF hfg.2.1, ?_⟩
  refine ⟨(canonCriterion_capLayered_iff LG p hF hfl).2 hcrit, by rw [← hord]; exact capGarden_order _,
    fun j => by rw [capGarden_sig_inl]; exact hfg.2.2 j, fun j => ?_, fun j => ⟨?_, ?_, ?_⟩⟩
  · rw [capGarden_sig_inr, capSigCaps_eq LG.garden hF ζ hsgn j, hfg.2.2 j]
  · exact (stem_iff_cap LG p hF).1 hstem j
  · exact (flowerKindOK_iff_cap LG p _ hF kind).1 hkind j
  · exact (patValid_iff_cap LG p hF j (pat j)).1 (hpat j)

/-- **The carrier on the capped garden** (backward). -/
theorem mem_carrier_of_capGlob (P : WTParams) (p N : ℕ) (hp : p < P.D) (hN : N ≤ P.N (p + 1) ^ 4)
    (kind : FlowerKind) (pat : Fin w → FixPat) (ζ : ℤˣ) {LG : LayeredGarden w} (hF : OneFlower LG.garden)
    (hm : ∀ ℓ, LG.garden.mark ℓ ≠ none → LG.garden.IsFlower ℓ)
    (hsig : ∀ j, LG.garden.sig j = (capLayered LG p).garden.sig (capσ w (.inl j)))
    (h : CapGlob P p N kind pat ζ (capLayered LG p)) : LG ∈ FC23.flowerCarrier P p N kind pat ζ := by
  obtain ⟨hcrit, hord, hsi, hsc, hj⟩ := h
  have hsig' : ∀ j : Fin w, LG.garden.sig j = (-1) ^ (j : ℕ) := fun j => (hsig j).trans (hsi j)
  have hstem : ∀ a, LG.OnStem a → LG.layer a = p := (stem_iff_cap LG p hF).2 fun j => (hj j).1
  have hfl : ∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ → LG.layer ℓ.toNode = p :=
    fun ℓ hℓ => hstem _ ⟨ℓ, hℓ, GNode.isDesc_refl _⟩
  have hord' : LG.garden.order = N := by rw [← hord]; exact (capGarden_order _).symm
  refine ⟨⟨isFlowerGarden_of LG.garden hF hm hsig', hstem, (canonCriterion_capLayered_iff LG p hF hfl).1 hcrit⟩,
    fun u _ => ?_, hord', (flowerKindOK_iff_cap LG p _ hF kind).2 fun j => (hj j).2.1, fun ℓ hℓ => ?_,
    fun j => (patValid_iff_cap LG p hF j (pat j)).2 (hj j).2.2⟩
  · exact (LG.attachedOrder_le_order p u).trans (by rw [hord']; exact hN.trans (N_fourth_le_N P hp))
  · have h1 := capSigCaps_of_flower LG.garden hF hℓ
    have h2 := hsc ℓ.1.1
    rw [capGarden_sig_inr, h1] at h2
    rw [hsig' ℓ.1.1]
    have := congrArg Neg.neg h2
    simpa using this

end WaveTurbulence.Flower.CapsComp
