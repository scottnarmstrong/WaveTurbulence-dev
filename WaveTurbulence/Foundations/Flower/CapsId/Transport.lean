/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsId.Kernel
public import WaveTurbulence.Foundations.Flower.MkDefs.Intrinsic
/-! # A2 CAPS-ID: transport of the flower weights to the capped garden (S-MARKED §4.1 row A2)

With cap trees `capJ w`, the flower notions of `LG` become the intrinsic capped notions of A1 MK-DEFS on
`capLayered LG p`: flowers are the non-cap leaves paired with a cap root (`isCapFlower_iff`), so stems, flower
parents and flower nodes transport. The weights transport accordingly (`OneFlower`, flowers in layer `p`):
- `frontierW_capLayered`: `Typed.frontierW` (per-tree radii extended by `none` at the caps);
- `stemFilterCap_capLayered`: `Cases.stemFilter → MkDefs.stemFilterCap`;
- `leafProdCap_capLayered`: `Typed.leafProd → MkDefs.leafProdCap` (pair profiles `capH h`);
- `sibWeightCap_capLayered`: `LayeredGarden.sibWeight → MkDefs.sibWeightCap`;
- `capFix_eq_fixCap`: `fixPat → MkDefs.fixCap` (B0's intrinsic pins; values `s`, `t`);
- `capOff_eq_offCap`: the dagger's removed phases `→ MkDefs.offCap`.
`flowerWeighted_coreF_eq_capSum` assembles them: the Core-F flower sum is a sum of `MkDefs.compValue` of the capped
gardens with the weight `selOK · markedWeight` at no selection (`kSel ≡ none`), i.e. exactly `MkAsm.CompData.val`'s
integrand. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsId
open TTree Finset WaveTurbulence.FlowerP7 WaveTurbulence.Flower.MkDefs

variable {w d : ℕ}

/-! ## Per-tree data on the capped garden -/

/-- Per-tree data extended by a default value at the caps. -/
def capExt {V : Type*} (f : Fin w → V) (v : V) : Fin (2 * w) → V :=
  fun c => Sum.elim f (fun _ => v) ((capσ w).symm c)

@[simp] theorem capExt_inl {V : Type*} (f : Fin w → V) (v : V) (j : Fin w) : capExt f v (capσ w (.inl j)) = f j := by
  simp [capExt]

@[simp] theorem capExt_inr {V : Type*} (f : Fin w → V) (v : V) (j : Fin w) : capExt f v (capσ w (.inr j)) = v := by
  simp [capExt]

/-- Pair-type profiles on the capped garden: `h` on pairs of original trees, `0` on pairs meeting a cap. The
value at cap pairs is never read by `leafProdCap`; `0` keeps the `S^{40d,40d}` bound and the support hypothesis of
`MarkedComponentBoundAt` at the cap indices. -/
def capH (h : ℕ → Fin w → Fin w → Mom d → ℝ) : ℕ → Fin (2 * w) → Fin (2 * w) → Mom d → ℝ :=
  fun q c c' => Sum.elim (fun j => Sum.elim (fun j' => h q j j') (fun _ _ => 0) ((capσ w).symm c'))
    (fun _ _ => 0) ((capσ w).symm c)

@[simp] theorem capH_inl (h : ℕ → Fin w → Fin w → Mom d → ℝ) (q : ℕ) (j j' : Fin w) :
    capH h q (capσ w (.inl j)) (capσ w (.inl j')) = h q j j' := by
  simp [capH]

@[simp] theorem capH_inr_left (h : ℕ → Fin w → Fin w → Mom d → ℝ) (q : ℕ) (j : Fin w) (c : Fin (2 * w))
    (x : Mom d) : capH h q (capσ w (.inr j)) c x = 0 := by
  simp [capH]

@[simp] theorem capH_inr_right (h : ℕ → Fin w → Fin w → Mom d → ℝ) (q : ℕ) (c : Fin (2 * w)) (j : Fin w)
    (x : Mom d) : capH h q c (capσ w (.inr j)) x = 0 := by
  obtain ⟨s, rfl⟩ := (capσ w).surjective c
  rcases s with i | i <;> simp [capH]

/-- The dagger data on the capped garden (zero vectors at the caps; never read there). -/
def capDag (dagger : Option (Fin w → Fin 3 → Mom d)) : Option (Fin (2 * w) → Fin 3 → Mom d) :=
  dagger.map fun c => capExt c fun _ => 0

/-! ## Intrinsic capped notions -/

theorem embL_fst_notMem (G : Garden w) (ℓ : GLeaf G.tree) : (embL G ℓ).1.1 ∉ capJ w :=
  capσ_inl_notMem_capJ ℓ.1.1

theorem capL_fst_mem (G : Garden w) (j : Fin w) : (capL G j).1.1 ∈ capJ w := capσ_inr_mem_capJ j

/-- **The capped flowers are the original flowers.** -/
theorem isCapFlower_iff (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden)
    (x : GLeaf (capLayered LG p).garden.tree) :
    IsCapFlower (capLayered LG p) (capJ w) x ↔ ∃ ℓ, LG.garden.IsFlower ℓ ∧ x = embL LG.garden ℓ := by
  rcases leaf_cases LG.garden x with ⟨ℓ, rfl⟩ | ⟨j, rfl⟩
  · unfold IsCapFlower
    constructor
    · rintro ⟨-, h2⟩
      refine ⟨ℓ, ?_, rfl⟩
      by_contra hn
      change ((capGarden LG.garden).pair (embL LG.garden ℓ)).1.1 ∈ capJ w at h2
      rw [capGarden_pair_nonflower _ hF hn] at h2
      exact embL_fst_notMem _ _ h2
    · rintro ⟨ℓ', hℓ', he⟩
      obtain rfl := embL_injective _ he
      refine ⟨embL_fst_notMem _ _, ?_⟩
      change ((capGarden LG.garden).pair (embL LG.garden ℓ)).1.1 ∈ capJ w
      rw [capGarden_pair_flower _ hF hℓ']
      exact capL_fst_mem _ _
  · unfold IsCapFlower
    constructor
    · rintro ⟨h1, -⟩
      exact absurd (capL_fst_mem _ _) h1
    · rintro ⟨ℓ, -, he⟩
      exact absurd he.symm (embL_ne_capL _ _ _)

theorem isParentOf_embL (G : Garden w) (b : GBranch G.tree) (ℓ : GLeaf G.tree) :
    (cBranch G b).IsParentOf (embL G ℓ) ↔ b.IsParentOf ℓ := by
  simp only [GBranch.IsParentOf, embL_val, cBranch_val, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq]

theorem isDesc_embN (G : Garden w) (a a' : GNode G.tree) : (embN G a).IsDesc (embN G a') ↔ a.IsDesc a' := by
  simp only [GNode.IsDesc, embN_val, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq]

theorem isCapFlowerParent_cBranch (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden)
    (b : GBranch LG.garden.tree) :
    IsCapFlowerParent (capLayered LG p) (capJ w) (cBranch LG.garden b) ↔ LG.garden.IsFlowerParent b := by
  unfold IsCapFlowerParent Garden.IsFlowerParent
  constructor
  · rintro ⟨x, hx, hp⟩
    obtain ⟨ℓ, hℓ, rfl⟩ := (isCapFlower_iff LG p hF x).1 hx
    exact ⟨ℓ, hℓ, (isParentOf_embL _ b ℓ).1 hp⟩
  · rintro ⟨ℓ, hℓ, hp⟩
    exact ⟨embL LG.garden ℓ, (isCapFlower_iff LG p hF _).2 ⟨ℓ, hℓ, rfl⟩, (isParentOf_embL _ b ℓ).2 hp⟩

theorem onCapStem_embN (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden) (a : GNode LG.garden.tree) :
    OnCapStem (capLayered LG p) (capJ w) (embN LG.garden a) ↔ LG.OnStem a := by
  unfold OnCapStem LayeredGarden.OnStem
  constructor
  · rintro ⟨x, hx, hd⟩
    obtain ⟨ℓ, hℓ, rfl⟩ := (isCapFlower_iff LG p hF x).1 hx
    exact ⟨ℓ, hℓ, (isDesc_embN _ a ℓ.toNode).1 hd⟩
  · rintro ⟨ℓ, hℓ, hd⟩
    exact ⟨embL LG.garden ℓ, (isCapFlower_iff LG p hF _).2 ⟨ℓ, hℓ, rfl⟩, (isDesc_embN _ a ℓ.toNode).2 hd⟩

/-- Capped flower nodes are the original flower nodes. -/
theorem capFlowerNode_iff (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden) (a : GNode LG.garden.tree) :
    (∃ x : GLeaf (capLayered LG p).garden.tree, IsCapFlower (capLayered LG p) (capJ w) x ∧
      x.toNode = embN LG.garden a) ↔ LG.IsFlowerNode a := by
  unfold LayeredGarden.IsFlowerNode
  constructor
  · rintro ⟨x, hx, he⟩
    obtain ⟨ℓ, hℓ, rfl⟩ := (isCapFlower_iff LG p hF x).1 hx
    exact ⟨ℓ, hℓ, embN_injective _ he⟩
  · rintro ⟨ℓ, hℓ, rfl⟩
    exact ⟨embL LG.garden ℓ, (isCapFlower_iff LG p hF _).2 ⟨ℓ, hℓ, rfl⟩, rfl⟩

/-- The capped stem set of an original tree is the stem set. -/
theorem stemSetCap_inl (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden) (j : Fin w) :
    stemSetCap (capLayered LG p) (capJ w) (capσ w (.inl j)) =
      (Cases.stemSet LG j).map (cBranch LG.garden).toEmbedding := by
  ext b
  obtain ⟨b, rfl⟩ := (cBranch LG.garden).surjective b
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
  simp only [stemSetCap, Cases.stemSet, Finset.mem_filter, Finset.mem_univ, true_and, cBranch_val,
    EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, cBranch_toNode, onCapStem_embN LG p hF,
    isCapFlowerParent_cBranch LG p hF]

/-- The capped stem set of a cap tree is empty. -/
theorem stemSetCap_inr (LG : LayeredGarden w) (p : ℕ) (j : Fin w) :
    stemSetCap (capLayered LG p) (capJ w) (capσ w (.inr j)) = ∅ := by
  ext b
  obtain ⟨b, rfl⟩ := (cBranch LG.garden).surjective b
  simp only [stemSetCap, Finset.mem_filter, Finset.mem_univ, true_and, cBranch_val,
    EmbeddingLike.apply_eq_iff_eq, reduceCtorEq, false_and, Finset.notMem_empty]

theorem prodDyadicCut_map {ι κ : Type*} (L : ℝ) (j : ℕ) (s : Finset ι) (e : ι ↪ κ) (y : κ → ℝ) :
    prodDyadicCut L j (s.map e) y = prodDyadicCut L j s (fun a => y (e a)) := by
  unfold prodDyadicCut
  simp only [Finset.prod_map]

/-! ## The transports -/

/-- Capped nodes with a given address are the embedded node. -/
theorem capLayer_eq_of_val (LG : LayeredGarden w) (p : ℕ) (x : GNode (capGarden LG.garden).tree)
    (a : GNode LG.garden.tree) (h : x.1 = (embN LG.garden a).1) : capLayer LG p x = LG.layer a := by
  rw [show x = embN LG.garden a from Subtype.ext h, capLayer_embN]

theorem parentLayer_embN (LG : LayeredGarden w) (p top : ℕ) (a : GNode LG.garden.tree) :
    (capLayered LG p).parentLayer top (embN LG.garden a) = LG.parentLayer top a := by
  unfold LayeredGarden.parentLayer
  by_cases h : a.1.2 = []
  · simp only [embN_val, h, ite_true]
  · simp only [embN_val, h, ite_false]
    exact capLayer_eq_of_val LG p _ _ rfl

theorem isTopLeaf_embN (LG : LayeredGarden w) (p q : ℕ) (a : GNode LG.garden.tree) :
    (capLayered LG p).IsTopLeaf q (embN LG.garden a) ↔ LG.IsTopLeaf q a := by
  unfold LayeredGarden.IsTopLeaf
  rw [parentLayer_embN]
  simp only [capLayer_embN, embN_val, capGarden_tree_inl]

theorem not_isTopLeaf_capN (LG : LayeredGarden w) (p q : ℕ) (j : Fin w) :
    ¬ (capLayered LG p).IsTopLeaf q (capN LG.garden j) := by
  unfold LayeredGarden.IsTopLeaf
  simp

/-- **Lemma 2.1(4)**: the top-layer order of an original tree is unchanged by capping. (So the flower kinds `Y`,
`W`, which force `N_{p+1} < topOrder`, are not ordinary `IsTrunc` gardens after capping.) -/
theorem topOrder_capLayered (LG : LayeredGarden w) (p q : ℕ) (j : Fin w) :
    (capLayered LG p).topOrder q (capσ w (.inl j)) = LG.topOrder q j := by
  unfold LayeredGarden.topOrder
  have : (Finset.univ.filter fun b : GBranch (capLayered LG p).garden.tree =>
      b.1.1 = capσ w (.inl j) ∧ (capLayered LG p).layer b.toNode = q) =
      (Finset.univ.filter fun b : GBranch LG.garden.tree => b.1.1 = j ∧ LG.layer b.toNode = q).map
        (cBranch LG.garden).toEmbedding := by
    ext b
    obtain ⟨b, rfl⟩ := (cBranch LG.garden).surjective b
    rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, cBranch_val, EmbeddingLike.apply_eq_iff_eq,
      Sum.inl.injEq, cBranch_toNode, capLayer_embN]
  rw [this, Finset.card_map]

/-- The caps have top-layer order `0`. -/
theorem topOrder_capLayered_cap (LG : LayeredGarden w) (p q : ℕ) (j : Fin w) :
    (capLayered LG p).topOrder q (capσ w (.inr j)) = 0 := by
  unfold LayeredGarden.topOrder
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro b _
  obtain ⟨b, rfl⟩ := (cBranch LG.garden).surjective b
  simp only [cBranch_val, EmbeddingLike.apply_eq_iff_eq, reduceCtorEq, false_and, not_false_eq_true]

/-- **Transport of the frontier cutoffs.** -/
theorem frontierW_capLayered (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden)
    (hfl : ∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ → LG.layer ℓ.toNode = p)
    (Rf : Fin w → Option ℝ) (k : GNode (capGarden LG.garden).tree → Mom d) :
    Typed.frontierW (capLayered LG p) p (capExt Rf none) k = Typed.frontierW LG p Rf (pullK LG.garden k) := by
  unfold Typed.frontierW
  rw [← (cNode LG.garden).prod_comp, Fintype.prod_sum_type]
  have hcap : ∀ c : GNode (capForest w), (if (capLayered LG p).IsTopLeaf p (cNode LG.garden (.inr c)) ∧
      (capLayered LG p).layer (cNode LG.garden (.inr c)) < p ∧
      ¬ (capLayered LG p).IsFlowerNode (cNode LG.garden (.inr c)) then
      (capExt Rf none (cNode LG.garden (.inr c)).1.1).elim 1 fun r => chi0 (‖k (cNode LG.garden (.inr c))‖ / r)
      else 1) = 1 := by
    intro c
    rw [capNodeF_eq c]
    exact ite_eq_right fun h => not_isTopLeaf_capN LG p p c.1.1 h.1
  rw [Finset.prod_congr rfl fun c _ => hcap c, Finset.prod_const_one, mul_one]
  refine Finset.prod_congr rfl fun a _ => ?_
  have hnf : ¬ (capLayered LG p).IsFlowerNode (embN LG.garden a) := fun ⟨x, hx, _⟩ =>
    capGarden_not_isFlower LG.garden hF x hx
  by_cases hc : LG.IsTopLeaf p a ∧ LG.layer a < p ∧ ¬ LG.IsFlowerNode a
  · have hc' : (capLayered LG p).IsTopLeaf p (embN LG.garden a) ∧
        (capLayered LG p).layer (embN LG.garden a) < p ∧ ¬ (capLayered LG p).IsFlowerNode (embN LG.garden a) :=
      ⟨(isTopLeaf_embN LG p p a).2 hc.1, by rw [capLayered_layer_embN]; exact hc.2.1, hnf⟩
    rw [ite_eq_left hc, ite_eq_left hc']
    simp only [embN_val, capExt_inl, pullK_apply]
  · have hc' : ¬ ((capLayered LG p).IsTopLeaf p (embN LG.garden a) ∧
        (capLayered LG p).layer (embN LG.garden a) < p ∧ ¬ (capLayered LG p).IsFlowerNode (embN LG.garden a)) := by
      rintro ⟨h1, h2, -⟩
      rw [capLayered_layer_embN] at h2
      refine hc ⟨(isTopLeaf_embN LG p p a).1 h1, h2, ?_⟩
      rintro ⟨ℓ, hℓ, rfl⟩
      rw [hfl ℓ hℓ] at h2
      exact lt_irrefl p h2
    rw [ite_eq_right hc, ite_eq_right hc']

/-- **Transport of the stem filters**: `stemFilter → stemFilterCap`. -/
theorem stemFilterCap_capLayered (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden) (L : ℝ)
    (σ : Fin w → Option ℕ) (k : GNode (capGarden LG.garden).tree → Mom d) :
    stemFilterCap (capLayered LG p) (capJ w) L (capExt σ none) k = Cases.stemFilter LG L σ (pullK LG.garden k) := by
  unfold stemFilterCap Cases.stemFilter
  rw [← (capσ w).prod_comp, Fintype.prod_sum_type]
  simp only [capExt_inr, Option.elim_none, Finset.prod_const_one, mul_one, capExt_inl]
  refine Finset.prod_congr rfl fun j _ => ?_
  rcases σ j with _ | i
  · rfl
  · simp only [Option.elim_some]
    rw [stemSetCap_inl LG p hF, prodDyadicCut_map]
    simp only [Equiv.coe_toEmbedding, omegaNode_cBranch]

theorem pairTrees_leaf (G : Garden w) (x : GLeaf G.tree) : LGSpine.pairTrees G x.1 = (x.1.1, (G.pair x).1.1) := by
  unfold LGSpine.pairTrees
  have hex : ∃ ℓ : GLeaf G.tree, ℓ.1 = x.1 := ⟨x, rfl⟩
  rw [dite_eq_left hex]
  have : hex.choose = x := Subtype.ext hex.choose_spec
  rw [this]

theorem typeProfiles_leaf (LG : LayeredGarden w) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (x : GLeaf LG.garden.tree) :
    LGSpine.typeProfiles LG h x.1 = h (LG.layer x.toNode) x.1.1 (LG.garden.pair x).1.1 := by
  unfold LGSpine.typeProfiles
  have hn : (x.1).2 ∈ (LG.garden.tree x.1.1).nodes := x.toNode.2
  rw [dite_eq_left hn, pairTrees_leaf]
  rfl

/-- **Transport of the pair-type leaf products**: `leafProd → leafProdCap`. -/
theorem leafProdCap_capLayered (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (k : GNode (capGarden LG.garden).tree → Mom d) :
    leafProdCap (capLayered LG p) (capJ w) (capH h) k = Typed.leafProd LG h (pullK LG.garden k) := by
  unfold leafProdCap Typed.leafProd inputLeaves
  rw [Finset.prod_filter, Finset.prod_filter, ← (cLeaf LG.garden).prod_comp, Fintype.prod_sum_type]
  have hcap : ∀ c : GLeaf (capForest w), (if (capLayered LG p).garden.sign (cLeaf LG.garden (.inr c)).toNode = 1 ∧
      (capLayered LG p).garden.mark (cLeaf LG.garden (.inr c)) = none then
      (if (cLeaf LG.garden (.inr c)).1.1 ∈ capJ w ∨ ((capLayered LG p).garden.pair (cLeaf LG.garden (.inr c))).1.1 ∈ capJ w
        then 1 else LGSpine.typeProfiles (capLayered LG p) (capH h) (cLeaf LG.garden (.inr c)).1
          (k (cLeaf LG.garden (.inr c)).toNode)) else 1) = 1 := by
    intro c
    rw [capLeafF_eq c]
    split_ifs with h1 h2
    · rfl
    · exact absurd (Or.inl (capL_fst_mem _ _)) h2
    · rfl
  rw [Finset.prod_congr rfl fun c _ => hcap c, Finset.prod_const_one, mul_one]
  refine Finset.prod_congr rfl fun ℓ _ => ?_
  by_cases hfl : LG.garden.IsFlower ℓ
  · have hm : LG.garden.mark ℓ ≠ none := by
      unfold Garden.IsFlower at hfl; rw [hfl]; exact Option.some_ne_none _
    rw [ite_eq_right (c := LG.garden.sign ℓ.toNode = 1 ∧ LG.garden.mark ℓ = none) (fun hc => hm hc.2)]
    have hJ : (embL LG.garden ℓ).1.1 ∈ capJ w ∨
        ((capLayered LG p).garden.pair (embL LG.garden ℓ)).1.1 ∈ capJ w := by
      right
      change ((capGarden LG.garden).pair (embL LG.garden ℓ)).1.1 ∈ capJ w
      rw [capGarden_pair_flower _ hF hfl]
      exact capL_fst_mem _ _
    rw [ite_eq_left hJ, ite_self]
  · have hpair : (capLayered LG p).garden.pair (embL LG.garden ℓ) = embL LG.garden (LG.garden.pair ℓ) :=
      capGarden_pair_nonflower _ hF hfl
    have hJ : ¬ ((embL LG.garden ℓ).1.1 ∈ capJ w ∨
        ((capLayered LG p).garden.pair (embL LG.garden ℓ)).1.1 ∈ capJ w) := by
      rw [hpair]
      rintro (h1 | h1) <;> exact embL_fst_notMem _ _ h1
    have hsm : ((capLayered LG p).garden.sign (embL LG.garden ℓ).toNode = 1 ∧
        (capLayered LG p).garden.mark (embL LG.garden ℓ) = none) ↔
        (LG.garden.sign ℓ.toNode = 1 ∧ LG.garden.mark ℓ = none) := by
      change ((capGarden LG.garden).sign (embN LG.garden ℓ.toNode) = 1 ∧
        (capGarden LG.garden).mark (embL LG.garden ℓ) = none) ↔ _
      rw [capGarden_sign_embN, capGarden_mark_nonflower _ hF hfl]
    by_cases hc : LG.garden.sign ℓ.toNode = 1 ∧ LG.garden.mark ℓ = none
    · rw [ite_eq_left (hsm.2 hc), ite_eq_right hJ, ite_eq_left hc, typeProfiles_leaf, typeProfiles_leaf, hpair]
      simp only [embL_toNode, capLayer_embN, embL_val, capH_inl, pullK_apply]
    · rw [ite_eq_right (fun h' => hc (hsm.1 h')), ite_eq_right hc]

/-- **Transport of the dagger sibling indicators**: `sibWeight → sibWeightCap`. -/
theorem sibWeightCap_capLayered (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden)
    (c : Fin w → Fin 3 → Mom d) (k : GNode (capGarden LG.garden).tree → Mom d) :
    sibWeightCap (capLayered LG p) (capJ w) (capExt c fun _ => 0) k = LG.sibWeight c (pullK LG.garden k) := by
  unfold sibWeightCap LayeredGarden.sibWeight
  rw [← (cBranch LG.garden).prod_comp]
  refine Finset.prod_congr rfl fun b _ => ?_
  by_cases hb : LG.garden.IsFlowerParent b
  · rw [ite_eq_left ((isCapFlowerParent_cBranch LG p hF b).2 hb), ite_eq_left hb]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [cBranch_child]
    by_cases hi : LG.IsFlowerNode (b.child i)
    · rw [ite_eq_left ((capFlowerNode_iff LG p hF _).2 hi), ite_eq_left hi]
    · rw [ite_eq_right (fun h => hi ((capFlowerNode_iff LG p hF _).1 h)), ite_eq_right hi]
      simp only [cBranch_val, capExt_inl, pullK_apply]
      exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)
  · rw [ite_eq_right (fun h => hb ((isCapFlowerParent_cBranch LG p hF b).1 h)), ite_eq_right hb]

/-! ## Pins and removed phases -/

/-- B0's intrinsic pins `fixCap` take only the values `s` and `t`. -/
theorem fixCap_values (LG : LayeredGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ)
    (b : GBranch LG.garden.tree) :
    (fixCap LG J pat t s b).isSome → fixCap LG J pat t s b = some s ∨ fixCap LG J pat t s b = some t := by
  intro h
  unfold fixCap at h ⊢
  by_cases hb : IsCapFlowerParent LG J b
  · rw [ite_eq_left hb]; exact Or.inl rfl
  · rw [ite_eq_right hb] at h ⊢
    generalize pat b.1.1 = q at h ⊢
    cases q with
    | plain => simp at h
    | dRoot => dsimp only at h ⊢; split_ifs at h ⊢ <;> simp_all
    | dParent => dsimp only at h ⊢; split_ifs at h ⊢ <;> simp_all
    | dChild i => dsimp only at h ⊢; split_ifs at h ⊢ <;> simp_all

/-- **Transport of the pins**: `fixPat → MkDefs.fixCap`. -/
theorem capFix_eq_fixCap (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden) (pat : Fin w → FixPat)
    (t s : ℝ) : capFix LG pat t s = fixCap (capLayered LG p) (capJ w) (capExt pat .plain) t s := by
  funext b
  obtain ⟨b, rfl⟩ := (cBranch LG.garden).surjective b
  unfold capFix fixCap LayeredGarden.fixPat
  rw [liftFix_cBranch]
  have hP := isCapFlowerParent_cBranch LG p hF b
  by_cases hb : LG.garden.IsFlowerParent b
  · rw [ite_eq_left hb, ite_eq_left (hP.2 hb)]
  · rw [ite_eq_right hb, ite_eq_right (fun h => hb (hP.1 h))]
    have hpat : capExt pat FixPat.plain (cBranch LG.garden b).1.1 = pat b.1.1 := capExt_inl pat _ b.1.1
    rw [hpat]
    rcases pat b.1.1 with _ | _ | _ | i
    · rfl
    · rfl
    · have he : (∃ c : GBranch (capLayered LG p).garden.tree,
          IsCapFlowerParent (capLayered LG p) (capJ w) c ∧ c.IsChildOf (cBranch LG.garden b)) ↔
          ∃ c : GBranch LG.garden.tree, LG.garden.IsFlowerParent c ∧ c.IsChildOf b := by
        constructor
        · rintro ⟨c, hc, hcb⟩
          obtain ⟨c, rfl⟩ := (cBranch LG.garden).surjective c
          exact ⟨c, (isCapFlowerParent_cBranch LG p hF c).1 hc, (isChildOf_cBranch _ c b).1 hcb⟩
        · rintro ⟨c, hc, hcb⟩
          exact ⟨cBranch LG.garden c, (isCapFlowerParent_cBranch LG p hF c).2 hc, (isChildOf_cBranch _ c b).2 hcb⟩
      simp only [he]
    · have he : (∃ c : GBranch (capLayered LG p).garden.tree,
          IsCapFlowerParent (capLayered LG p) (capJ w) c ∧ (cBranch LG.garden b).1.1 = c.1.1 ∧
            (cBranch LG.garden b).1.2 = c.1.2 ++ [i]) ↔
          ∃ c : GBranch LG.garden.tree, LG.garden.IsFlowerParent c ∧ b.1.1 = c.1.1 ∧ b.1.2 = c.1.2 ++ [i] := by
        constructor
        · rintro ⟨c, hc, h1, h2⟩
          obtain ⟨c, rfl⟩ := (cBranch LG.garden).surjective c
          simp only [cBranch_val, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq] at h1 h2
          exact ⟨c, (isCapFlowerParent_cBranch LG p hF c).1 hc, h1, h2⟩
        · rintro ⟨c, hc, h1, h2⟩
          refine ⟨cBranch LG.garden c, (isCapFlowerParent_cBranch LG p hF c).2 hc, ?_, ?_⟩
          · simp only [cBranch_val, h1]
          · simp only [cBranch_val, h2]
      simp only [he]

/-- The transported flower pins take only the values `s` and `t`. -/
theorem capFix_values (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden) (pat : Fin w → FixPat) (t s : ℝ)
    (b : GBranch (capGarden LG.garden).tree) :
    (capFix LG pat t s b).isSome → capFix LG pat t s b = some s ∨ capFix LG pat t s b = some t := by
  rw [capFix_eq_fixCap LG p hF]
  exact fixCap_values (capLayered LG p) (capJ w) (capExt pat .plain) t s b

/-- **Transport of the removed phases.** -/
theorem capOff_eq_offCap (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden)
    (dagger : Option (Fin w → Fin 3 → Mom d)) :
    capOff LG dagger = offCap (capLayered LG p) (capJ w) (capDag dagger).isSome := by
  unfold capOff offCap liftOff capDag
  rcases dagger with _ | c
  · simp
  · simp only [Option.isSome_some, ite_true, Option.map_some]
    ext b
    obtain ⟨b, rfl⟩ := (cBranch LG.garden).surjective b
    rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, isCapFlowerParent_cBranch LG p hF]

/-! ## The Core-F flower sum as a sum of marked component values -/

/-- On the carrier, flowers lie in layer `p` (they are on the stem). -/
theorem flower_layer_of_isCanonH {p : ℕ} {LG : LayeredGarden w} (h : IsCanonH (p + 1) LG)
    (ℓ : GLeaf LG.garden.tree) (hℓ : LG.garden.IsFlower ℓ) : LG.layer ℓ.toNode = p :=
  h.2.1 _ ⟨ℓ, hℓ, GNode.isDesc_refl _⟩

@[simp] theorem selOK_none {w' : ℕ} (LG' : LayeredGarden w') (J : Finset (Fin w')) :
    selOK LG' J (fun _ => none) = 1 := by
  simp [selOK]

@[simp] theorem selCap_none {w' : ℕ} (LG' : LayeredGarden w') (J : Finset (Fin w')) :
    selCap LG' J (fun _ => none) = fun _ => none := rfl

/-- The capped weight of the Core-F integrand is the marked weight with no selected vertices. -/
theorem capW_coreF_marked (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden)
    (hfl : ∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ → LG.layer ℓ.toNode = p) (L : ℝ)
    (Rf : Fin w → Option ℝ) (σ : Fin w → Option ℕ) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    (dagger : Option (Fin w → Fin 3 → Mom d)) (Rs : Fin (2 * w) → ℝ) :
    capW LG dagger (fun k => Typed.frontierW LG p Rf k * Cases.stemFilter LG L σ k * Typed.leafProd LG h k) =
      markedWeight (capLayered LG p) (capJ w) p L (capExt Rf none) (capExt σ none) (fun _ => none) Rs (capH h)
        (capDag dagger) := by
  funext k
  unfold capW pullW markedWeight
  rw [frontierW_capLayered LG p hF hfl, stemFilterCap_capLayered LG p hF, leafProdCap_capLayered LG p hF]
  have hsel : selWeightCap (capLayered LG p) (capJ w) (fun _ => none) Rs k = 1 := by
    simp [selWeightCap]
  rw [hsel]
  rcases dagger with _ | c
  · simp [capDag]
  · simp only [capDag, Option.map_some, Option.elim_some, sibWeightCap_capLayered LG p hF]
    ring

/-- The capped weight of the Core-F integrand in the form of `MkAsm.CompData.val` (`selOK · markedWeight` at
`kSel ≡ none`). -/
theorem capW_coreF (LG : LayeredGarden w) (p : ℕ) (hF : OneFlower LG.garden)
    (hfl : ∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ → LG.layer ℓ.toNode = p) (L : ℝ)
    (Rf : Fin w → Option ℝ) (σ : Fin w → Option ℕ) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    (dagger : Option (Fin w → Fin 3 → Mom d)) (Rs : Fin (2 * w) → ℝ) :
    capW LG dagger (fun k => Typed.frontierW LG p Rf k * Cases.stemFilter LG L σ k * Typed.leafProd LG h k) =
      fun k => selOK (capLayered LG p) (capJ w) (fun _ => none) *
        markedWeight (capLayered LG p) (capJ w) p L (capExt Rf none) (capExt σ none)
          (selCap (capLayered LG p) (capJ w) (fun _ => none)) Rs (capH h) (capDag dagger) k := by
  rw [capW_coreF_marked LG p hF hfl L Rf σ h dagger Rs]
  funext k
  rw [selOK_none, one_mul, selCap_none]

/-- **CAPS-ID, Core-F form.** The Core-F flower sum is the sum over the frozen carrier of the marked component
values `compValue` of the capped gardens, with B0's intrinsic pins `fixCap`, removed phases `offCap` and the weight
`selOK · markedWeight` at no selection (frontier radii, stem filters, pair profiles and dagger extended to the
caps): exactly the integrand of `MkAsm.CompData.val` with `kSel ≡ none`. -/
theorem flowerWeighted_coreF_eq_capSum (P : WTParams) (p N : ℕ) (kind : FlowerKind) (pat : Fin w → FixPat)
    (dagger : Option (Fin w → Fin 3 → Mom P.d)) (h : ℕ → Fin w → Fin w → Mom P.d → ℝ)
    (Rf : Fin w → Option ℝ) (σ : Fin w → Option ℕ) (Rs : Fin (2 * w) → ℝ) (ζ : ℤˣ) (t s : ℝ)
    (n n' : Fin P.d → ℤ) :
    FC23.flowerWeighted P (fun _ _ => 1) p N kind pat dagger
        (fun LG k => Typed.frontierW LG p Rf k * Cases.stemFilter LG P.L σ k * Typed.leafProd LG h k) ζ t s n n' =
      ∑ LG ∈ (FC23.flowerCarrier_finite P p N kind pat ζ).toFinset,
        compValue P (capLayered LG p) (fixCap (capLayered LG p) (capJ w) (capExt pat .plain) t s)
          (offCap (capLayered LG p) (capJ w) (capDag dagger).isSome)
          (fun k => selOK (capLayered LG p) (capJ w) (fun _ => none) *
            markedWeight (capLayered LG p) (capJ w) p P.L (capExt Rf none) (capExt σ none)
              (selCap (capLayered LG p) (capJ w) (fun _ => none)) Rs (capH h) (capDag dagger) k)
          t (capRoots (fun _ => n) n') := by
  rw [flowerWeighted_eq_capSum]
  refine Finset.sum_congr rfl fun LG hLG => ?_
  have hc : LG ∈ FC23.flowerCarrier P p N kind pat ζ := (Set.Finite.mem_toFinset _).1 hLG
  have hF := oneFlower_of_isFlowerGarden hc.1.1
  have hfl := flower_layer_of_isCanonH hc.1
  unfold compValue
  rw [capFix_eq_fixCap LG p hF, capOff_eq_offCap LG p hF, capW_coreF LG p hF hfl]

end WaveTurbulence.Flower.CapsId
