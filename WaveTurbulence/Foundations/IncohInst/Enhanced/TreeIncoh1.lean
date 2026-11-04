/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Links.Incoh1
public import WaveTurbulence.Foundations.IncohInst.Links.TreeLinks

/-!
# The unimodular change of variables for regular trees (TARGET L1060–L1092)

The tree case of TARGET (incohproof1)–(incohproof2), used for `𝒦_𝒯^*` in the proof of Prop 5.1
(TARGET L1060: "By the same arguments as in the `𝒦_𝒬^*` case, ..."). For a paired-tree carrier `G`
(`Garden 1`) decoded by a chain code `X` (`RegChain.DecodesTree`), with `n(𝒯) = 2n`:

* the lone leaf carries the root vector, `k_{ℓ_lo} = k` (`tree_root_eq_lone`);
* decorations with root `r` correspond bijectively to the link parameters `(x_𝔫, y_𝔫)_{𝔫 ∈ 𝒩^ch}`
  (`treeDecEquiv`);
* there are integer matrices `T`, `S`, inverse to each other, between the leaf coordinates
  `(k_{ℓ_lo}; k_ℓ for the 2n paired leaves of sign +)` and the link coordinates
  `(k; x_j, y_j)`: `tree_incoh_unimodular`. Here `T ℓ k = 1` for every leaf and the `k`-row of `S`
  is `k = k_{ℓ_lo}`; there is no constraint among the paired leaves (unlike (incohproof1) for
  couples).
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg Finset

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

/-! ### Folding the pairing in a garden with marked leaves -/

/-- The paired leaves of sign `+`. -/
def plusPaired {w : ℕ} (G : Garden w) : Finset (GLeaf G.tree) :=
  univ.filter fun ℓ => G.sign ℓ.toNode = 1 ∧ G.pair ℓ ≠ ℓ

/-- The marked (unpaired) leaves. -/
def markedLeaves {w : ℕ} (G : Garden w) : Finset (GLeaf G.tree) :=
  univ.filter fun ℓ => G.pair ℓ = ℓ

/-- A leaf sum folds onto the paired `+` leaves and the marked leaves (`k_{ℓ'} = k_ℓ` on pairs). -/
theorem sum_fold_pairs_marked {w : ℕ} {G : Garden w} {κ : GNode G.tree → V}
    (hκ : IsDecoration G κ) (f : GLeaf G.tree → ℤ) :
    ∑ ℓ, f ℓ • κ ℓ.toNode = ∑ ℓ ∈ plusPaired G, (f ℓ + f (G.pair ℓ)) • κ ℓ.toNode +
      ∑ ℓ ∈ markedLeaves G, f ℓ • κ ℓ.toNode := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun ℓ : GLeaf G.tree => G.pair ℓ = ℓ), add_comm]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not (univ.filter fun ℓ : GLeaf G.tree => ¬ G.pair ℓ = ℓ)
    (fun ℓ : GLeaf G.tree => G.sign ℓ.toNode = 1), Finset.filter_filter, Finset.filter_filter]
  have hP : (univ.filter fun ℓ : GLeaf G.tree => ¬G.pair ℓ = ℓ ∧ G.sign ℓ.toNode = 1) =
      plusPaired G := by
    ext ℓ; simp [plusPaired, and_comm]
  have h2 : ∑ ℓ ∈ univ.filter (fun ℓ : GLeaf G.tree => ¬G.pair ℓ = ℓ ∧ ¬G.sign ℓ.toNode = 1),
      f ℓ • κ ℓ.toNode = ∑ ℓ ∈ plusPaired G, f (G.pair ℓ) • κ ℓ.toNode := by
    refine Finset.sum_nbij' G.pair G.pair ?_ ?_ ?_ ?_ ?_
    · intro ℓ hℓ
      have hℓ' : ¬G.pair ℓ = ℓ ∧ ¬G.sign ℓ.toNode = 1 := by simpa using hℓ
      have hs : G.sign (G.pair ℓ).toNode = -G.sign ℓ.toNode := G.pair_sign ℓ hℓ'.1
      have h1 : G.sign (G.pair ℓ).toNode = 1 := by
        rcases Int.units_eq_one_or (G.sign ℓ.toNode) with h | h
        · exact absurd h hℓ'.2
        · rw [hs, h, neg_neg]
      have h3 : G.pair (G.pair ℓ) ≠ G.pair ℓ := by
        rw [G.pair_pair]; exact fun h => hℓ'.1 h.symm
      simpa [plusPaired] using ⟨h1, h3⟩
    · intro ℓ hℓ
      have hℓ' : G.sign ℓ.toNode = 1 ∧ G.pair ℓ ≠ ℓ := by simpa [plusPaired] using hℓ
      have hs : G.sign (G.pair ℓ).toNode = -G.sign ℓ.toNode := G.pair_sign ℓ hℓ'.2
      have h1 : ¬G.sign (G.pair ℓ).toNode = 1 := by rw [hs, hℓ'.1]; decide
      have h3 : ¬G.pair (G.pair ℓ) = G.pair ℓ := by
        rw [G.pair_pair]; exact fun h => hℓ'.2 h.symm
      simpa using ⟨h3, h1⟩
    · intro ℓ _; exact G.pair_pair ℓ
    · intro ℓ _; exact G.pair_pair ℓ
    · intro ℓ _
      rw [G.pair_pair, ← hκ.2 ℓ]
  rw [hP, h2, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ℓ _ => (add_smul _ _ _).symm

/-! ### The lone leaf of a decoded tree -/

variable {G : Garden 1} {X : RegChain}

theorem fin_one_eq (x : Fin 1) : x = 0 := Subsingleton.elim _ _

theorem ite_fin_one {α : Type*} (x : Fin 1) (a b : α) : (if x = 0 then a else b) = a :=
  by simp [fin_one_eq x]

theorem tree_pair_eq_iff (hX : X.DecodesTree G) (ℓ : GLeaf G.tree) :
    G.pair ℓ = ℓ ↔ ℓ.1.2 = X.lonePath := by
  rw [G.pair_eq_iff, hX.2.1 ℓ]
  split_ifs with h <;> simp [h]

theorem lone_mem_leaves (hX : X.DecodesTree G) : X.lonePath ∈ (G.tree 0).leaves := by
  have h := chain_leafAddresses X (G.sig 0) .leaf ((0 : Fin 1), ([] : Path))
  have hm : addrExt ((0 : Fin 1), ([] : Path)) X.lonePath ∈
      leafAddresses (X.plug (G.sig 0) .leaf) ((0 : Fin 1), ([] : Path)) := by
    rw [h]; simp
  rw [tree_eq_plug hX]
  simp only [leafAddresses, Finset.mem_image, addrExt] at hm
  obtain ⟨q, hq, hqe⟩ := hm
  have : q = X.lonePath := by simpa using congrArg Prod.snd hqe
  rw [← this]; exact hq

/-- The lone leaf `ℓ_lo` of a decoded tree carrier. -/
def loneLeaf (hX : X.DecodesTree G) : GLeaf G.tree := ⟨((0 : Fin 1), X.lonePath), lone_mem_leaves hX⟩

theorem markedLeaves_eq (hX : X.DecodesTree G) : markedLeaves G = {loneLeaf hX} := by
  ext ℓ
  simp only [markedLeaves, mem_filter, mem_univ, true_and, mem_singleton, tree_pair_eq_iff hX]
  constructor
  · intro h; exact Subtype.ext (Prod.ext (fin_one_eq _) h)
  · rintro rfl; rfl

/-- `pathSign 1 p = ζ · ζ_ℓ` in a tree of sign `ζ`. -/
theorem pathSign_one_eq (ℓ : GLeaf G.tree) :
    ((pathSign 1 ℓ.1.2 : ℤˣ) : ℤ) = (G.sig 0 : ℤ) * (G.sign ℓ.toNode : ℤ) := by
  show _ = _ * ((pathSign (G.sig ℓ.1.1) ℓ.1.2 : ℤˣ) : ℤ)
  rw [fin_one_eq ℓ.1.1]
  simp only [pathSign, Units.val_mul, one_mul]
  rw [← mul_assoc, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_mul]

theorem tree_root_eq_pathSign_lone (hX : X.DecodesTree G) {κ : GNode G.tree → V}
    (hκ : IsDecoration G κ) :
    κ (GNode.root G.tree 0) = ((pathSign 1 X.lonePath : ℤˣ) : ℤ) • κ (loneLeaf hX).toNode := by
  rw [root_eq_sum_leaves hκ, sum_fold_pairs_marked hκ, markedLeaves_eq hX, sum_singleton]
  have h0 : ∑ ℓ ∈ plusPaired G, ((if ℓ.1.1 = 0 then ((pathSign 1 ℓ.1.2 : ℤˣ) : ℤ) else 0) +
      (if (G.pair ℓ).1.1 = 0 then ((pathSign 1 (G.pair ℓ).1.2 : ℤˣ) : ℤ) else 0)) •
        κ ℓ.toNode = 0 := by
    refine Finset.sum_eq_zero fun ℓ hℓ => ?_
    have hℓ' : G.sign ℓ.toNode = 1 ∧ G.pair ℓ ≠ ℓ := by simpa [plusPaired] using hℓ
    have hs : G.sign (G.pair ℓ).toNode = -G.sign ℓ.toNode := G.pair_sign ℓ hℓ'.2
    rw [ite_fin_one, ite_fin_one, pathSign_one_eq, pathSign_one_eq, hs, Units.val_neg, mul_neg,
      add_neg_cancel, zero_smul]
  rw [h0, zero_add, ite_fin_one]
  rfl

/-- `ℓ_lo` has path sign `+` (it has the sign of the root). -/
theorem pathSign_lone (hX : X.DecodesTree G) : ((pathSign 1 X.lonePath : ℤˣ) : ℤ) = 1 := by
  have h := tree_root_eq_pathSign_lone hX (κ := fun _ => (1 : ℤ)) ⟨fun _ => by norm_num, fun _ => rfl⟩
  simpa using h.symm

/-- **The lone leaf carries the root vector**: `k_{ℓ_lo} = k_𝔯`. -/
theorem tree_root_eq_lone (hX : X.DecodesTree G) {κ : GNode G.tree → V} (hκ : IsDecoration G κ) :
    κ (GNode.root G.tree 0) = κ (loneLeaf hX).toNode := by
  rw [tree_root_eq_pathSign_lone hX hκ, pathSign_lone hX, one_smul]

/-! ### Decorations of trees ↔ link parameters -/

/-- The chosen node of the `j`-th link of a tree code. -/
def treeChosen (X : RegChain) (ζ : ℤˣ) (j : Fin (X.treeLinks ζ).length) : Fin 1 × Path :=
  ((X.treeLinks ζ).get j).1

theorem tree_chosen_nodup (X : RegChain) (ζ : ℤˣ) : ((X.treeLinks ζ).map Prod.fst).Nodup := by
  have hnd := tree_links_flat_nodup X ζ
  refine List.Nodup.sublist ?_ hnd
  clear hnd
  induction X.treeLinks ζ with
  | nil => simp [flatPairs]
  | cons p L ih =>
    simp only [List.map_cons, flatPairs, List.flatMap_cons, List.cons_append] at ih ⊢
    exact List.Sublist.cons_cons _ (List.Sublist.cons _ ih)

theorem idxOf_treeChosen (X : RegChain) (ζ : ℤˣ) (j : Fin (X.treeLinks ζ).length) :
    ((X.treeLinks ζ).map Prod.fst).idxOf (treeChosen X ζ j) = j := by
  have := (tree_chosen_nodup X ζ).idxOf_getElem j (by simp)
  simpa [treeChosen] using this

/-- The tree parameters as a function of addresses (zero away from `𝒩^ch`). -/
def treeParamFun (X : RegChain) (ζ : ℤˣ) (θ : Fin (X.treeLinks ζ).length → V × V)
    (z : Fin 1 × Path) : V × V :=
  if h : ((X.treeLinks ζ).map Prod.fst).idxOf z < (X.treeLinks ζ).length then θ ⟨_, h⟩ else 0

theorem treeParamFun_chosen (X : RegChain) (ζ : ℤˣ) (θ : Fin (X.treeLinks ζ).length → V × V)
    (j : Fin (X.treeLinks ζ).length) : treeParamFun X ζ θ (treeChosen X ζ j) = θ j := by
  have hidx := idxOf_treeChosen X ζ j
  unfold treeParamFun
  split_ifs with h
  · congr 1
    exact Fin.ext hidx
  · exact absurd (hidx ▸ j.2) h

/-- The decorations of a tree carrier with root value `r`. -/
def DecRT (G : Garden 1) (V : Type*) [AddCommGroup V] (r : V) : Type _ :=
  {κ : GNode G.tree → V // IsDecoration G κ ∧ κ (GNode.root G.tree 0) = r}

theorem tree_mem_nodes_iff (hX : X.DecodesTree G) (x : Fin 1 × Path) :
    x.2 ∈ (G.tree x.1).nodes ↔ x ∈ pairEndpoints (X.treeLinks (G.sig 0)) ∪
      pairEndpoints (X.pairsAt (G.sig 0) (0, [])) ∪ {((0 : Fin 1), X.lonePath)} := by
  rw [Finset.mem_union, Finset.mem_union, tree_mem_pairEndpoints_links_iff hX,
    Comb.TreePath.mem_nodes_iff]
  have hl : x.2 ∈ (G.tree x.1).leaves ↔
      x ∈ pairEndpoints (X.pairsAt (G.sig 0) (0, [])) ∪ {((0 : Fin 1), X.lonePath)} := by
    have h := chain_leafAddresses X (G.sig 0) .leaf ((0 : Fin 1), ([] : Path))
    rw [leafAddresses_leaf] at h
    have e : addrExt ((0 : Fin 1), ([] : Path)) X.lonePath = ((0 : Fin 1), X.lonePath) := by
      simp [addrExt]
    rw [e] at h
    rw [← h, fin_one_eq x.1, tree_eq_plug hX]
    obtain ⟨j, p⟩ := x
    simp [leafAddresses, addrExt, fin_one_eq j]
  rw [hl, Finset.mem_union]; tauto

/-- **A code decoration of a tree code restricts to a decoration of the carrier.** -/
theorem isDecoration_of_chainDec (hX : X.DecodesTree G) {f : Fin 1 × Path → V}
    (h : ChainDec f X (G.sig 0) (0, [])) : IsDecoration G (fun a : GNode G.tree => f a.1) := by
  constructor
  · intro b
    have hx : b.1 ∈ pairEndpoints (X.treeLinks (G.sig 0)) :=
      (tree_mem_pairEndpoints_links_iff hX b.1).2 b.2
    exact chainDec_nodeRel f X _ _ h _ hx
  · intro ℓ
    by_cases hl : ℓ.1.2 = X.lonePath
    · rw [(tree_pair_eq_iff hX ℓ).2 hl]
    · have hm := hX.2.2 ℓ hl
      have hp := chainDec_pairs f X _ _ h
      rcases List.mem_append.mp hm with hm | hm
      · exact hp _ hm
      · obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hm
        have := hp q hq
        obtain ⟨q1, q2⟩ := q
        simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hqe
        obtain ⟨rfl, rfl⟩ := hqe
        exact this.symm

theorem xv_extend_restrict' {w : ℕ} {G' : Garden w} (g : Fin w × Path → V) {x : Fin w × Path}
    (hx : x.2 ∈ (G'.tree x.1).branching) :
    xv (extend (fun a : GNode G'.tree => g a.1)) x = xv g x ∧
      yv (extend (fun a : GNode G'.tree => g a.1)) x = yv g x := by
  constructor
  · have := xv_extend (fun a : GNode G'.tree => g a.1) ⟨x, hx⟩
    rw [this]; rfl
  · have := yv_extend (fun a : GNode G'.tree => g a.1) ⟨x, hx⟩
    rw [this]; rfl

/-- The link parameters of a tree decoration. -/
def treeDecParams (X : RegChain) {r : V} (κ : DecRT G V r) :
    Fin (X.treeLinks (G.sig 0)).length → V × V :=
  fun j => (xv (extend κ.1) (treeChosen X _ j), yv (extend κ.1) (treeChosen X _ j))

/-- The tree decoration with root value `r` and link parameters `θ`. -/
def treeDecOfParams (hX : X.DecodesTree G) (r : V) (θ : Fin (X.treeLinks (G.sig 0)).length → V × V) :
    DecRT G V r :=
  ⟨fun a => chainVal (treeParamFun X (G.sig 0) θ) X (G.sig 0) (0, []) r (fun _ => r) a.1,
    isDecoration_of_chainDec hX (chainDec_chainVal _ X _ _ r _ rfl),
    chainVal_root _ X _ _ r _ rfl⟩

theorem lone_under (X : RegChain) :
    Under (addrExt ((0 : Fin 1), ([] : Path)) X.lonePath) ((0 : Fin 1), X.lonePath) := by
  have e : addrExt ((0 : Fin 1), ([] : Path)) X.lonePath = ((0 : Fin 1), X.lonePath) := by
    simp [addrExt]
  rw [e]; exact under_refl _

/-- **The change of variables for regular trees**: decorations with root value `r` correspond
bijectively to the link parameters `(x_𝔫, y_𝔫)_{𝔫 ∈ 𝒩^ch}`. -/
def treeDecEquiv (hX : X.DecodesTree G) (r : V) :
    DecRT G V r ≃ (Fin (X.treeLinks (G.sig 0)).length → V × V) where
  toFun := treeDecParams X
  invFun := treeDecOfParams hX r
  left_inv κ := by
    apply Subtype.ext
    funext a
    have hd := chainDec_of_decoration hX κ.2.1
    have hr : extend κ.1 ((0 : Fin 1), ([] : Path)) = r :=
      (extend_node κ.1 (GNode.root G.tree 0)).trans κ.2.2
    have hθ : ∀ l ∈ X.treeLinks (G.sig 0),
        xv (extend κ.1) l.1 = (treeParamFun X (G.sig 0) (treeDecParams X κ) l.1).1 ∧
        yv (extend κ.1) l.1 = (treeParamFun X (G.sig 0) (treeDecParams X κ) l.1).2 := by
      intro l hl
      obtain ⟨j, rfl⟩ := List.get_of_mem hl
      rw [show ((X.treeLinks (G.sig 0)).get j).1 = treeChosen X (G.sig 0) j from rfl,
        treeParamFun_chosen]
      exact ⟨rfl, rfl⟩
    have hmem := (tree_mem_nodes_iff hX a.1).1 a.2
    rw [Finset.mem_union, Finset.mem_singleton] at hmem
    rcases hmem with hmem | hmem
    · have := chainDec_determined (treeParamFun X (G.sig 0) (treeDecParams X κ)) X _ _ r
        (fun _ => r) rfl (extend κ.1) hd hr hθ a.1 hmem
      rw [extend_node] at this
      exact this.symm
    · have ha : a = (loneLeaf hX).toNode := Subtype.ext hmem
      subst ha
      show chainVal _ X _ _ r (fun _ => r) ((0 : Fin 1), X.lonePath) = _
      rw [chainVal_lone _ X _ _ r _ _ (lone_under X), ← tree_root_eq_lone hX κ.2.1, κ.2.2]
  right_inv θ := by
    funext j
    have hl : (X.treeLinks (G.sig 0)).get j ∈ X.treeLinks (G.sig 0) := List.get_mem _ _
    have hb := (tree_mem_pairEndpoints_links_iff hX _).1
      ((mem_pairEndpoints_iff _ _).2 ⟨_, hl, Or.inl rfl⟩)
    have hp := chainVal_params (treeParamFun X (G.sig 0) θ) X (G.sig 0) ((0 : Fin 1), ([] : Path)) r
      (fun _ => r) rfl _ (fun _ _ _ => rfl) _ hl
    obtain ⟨e1, e2⟩ := xv_extend_restrict' (G' := G)
      (chainVal (treeParamFun X (G.sig 0) θ) X (G.sig 0) (0, []) r (fun _ => r)) hb
    simp only [treeDecParams, treeDecOfParams, treeChosen]
    rw [e1, e2, hp.1, hp.2, show ((X.treeLinks (G.sig 0)).get j).1 =
      treeChosen X (G.sig 0) j from rfl, treeParamFun_chosen]

theorem treeDecParams_treeDecOfParams (hX : X.DecodesTree G) (r : V)
    (θ : Fin (X.treeLinks (G.sig 0)).length → V × V) :
    treeDecParams X (treeDecOfParams hX r θ) = θ :=
  (treeDecEquiv hX r).right_inv θ

end WaveTurbulence.Links
