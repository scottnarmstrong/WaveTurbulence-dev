/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Enhanced.TreeIncoh1

/-!
# The unimodular matrices for regular trees (TARGET L1060–L1092)

The tree analogue of `incoh_unimodular` (TARGET (incohproof1) for `𝒦_𝒯^*`):

* `tree_node_linear`: every node value of the tree decoration with root `r` and link parameters
  `(x_j, y_j)` is `r + ∑_j (A_j x_j + B_j y_j)` with integers `A_j, B_j` independent of the group;
* `tree_incoh_unimodular`: integer matrices `T` (leaf coordinates × link coordinates) and `S`, with
  `T * S = 1`, `S * T = 1`, `T ℓ k = 1`, and `S`'s `k`-row `k = k_{ℓ_lo}`; the leaf coordinates are
  `k_{ℓ_lo}` and `k_ℓ` for the `2n` paired leaves `ℓ` of sign `+`, the link coordinates
  `(k; x_j, y_j)`;
* `treeLinkCoords_surjective`: every link coordinate vector comes from a decoration.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg Finset

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W] {w : ℕ}

/-! ### Linearity of the chain construction -/

theorem fun_zero_add_const (r : V) :
    ((fun _ => (0 : V)) + (fun _ => r) : Fin w × Path → V) = fun _ => r := by
  funext; simp

theorem chainVal_zero (X : RegChain) (ζ : ℤˣ) (a z : Fin w × Path) :
    chainVal (0 : Fin w × Path → V × V) X ζ a 0 (fun _ => 0) z = 0 := by
  have h := chainVal_add (V := V) 0 0 X ζ a 0 0 (fun _ => 0) (fun _ => 0) z
  rw [add_zero, add_zero, fun_zero_add_const] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

/-- The chain construction with root value `0`, as an additive map of the parameters. -/
def chainValHom (X : RegChain) (ζ : ℤˣ) (a z : Fin w × Path) : (Fin w × Path → V × V) →+ V where
  toFun θ := chainVal θ X ζ a 0 (fun _ => 0) z
  map_zero' := chainVal_zero X ζ a z
  map_add' θ₁ θ₂ := by
    have := chainVal_add θ₁ θ₂ X ζ a 0 0 (fun _ => 0) (fun _ => 0) z
    rwa [add_zero, fun_zero_add_const] at this

/-- With zero parameters the chain construction is constant on the code and below the lone
position. -/
theorem chainVal_const (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (r : V) (z : Fin w × Path)
    (hz : z ∈ pairEndpoints (X.linksAt ζ a) ∪ pairEndpoints (X.pairsAt ζ a) ∨
      Under (addrExt a X.lonePath) z) :
    chainVal (0 : Fin w × Path → V × V) X ζ a r (fun _ => r) z = r := by
  rcases hz with hz | hz
  · have hd : ChainDec (fun _ => r) X ζ a :=
      chainDec_of_lists _ X ζ a (fun x _ => by unfold NodeRel; abel) (fun _ _ => rfl)
    exact (chainDec_determined 0 X ζ a r (fun _ => r) rfl (fun _ => r) hd rfl
      (fun l _ => by simp [xv, yv]) z hz).symm
  · exact chainVal_lone _ X ζ a r _ z hz

variable {G : Garden 1} {X : RegChain}

/-- `treeParamFun` as an additive map. -/
def treeParamFunHom (X : RegChain) (ζ : ℤˣ) :
    (Fin (X.treeLinks ζ).length → V × V) →+ (Fin 1 × Path → V × V) where
  toFun := treeParamFun X ζ
  map_zero' := by funext z; unfold treeParamFun; split_ifs <;> rfl
  map_add' θ₁ θ₂ := by
    funext z; unfold treeParamFun
    by_cases h : ((X.treeLinks ζ).map Prod.fst).idxOf z < (X.treeLinks ζ).length
    · simp only [h, ↓reduceDIte, Pi.add_apply]
    · simp only [h, ↓reduceDIte, Pi.add_apply, add_zero]

theorem treeParamFun_map (φ : V →+ W) (ζ : ℤˣ) (θ : Fin (X.treeLinks ζ).length → V × V)
    (z : Fin 1 × Path) :
    treeParamFun X ζ (fun j => (φ (θ j).1, φ (θ j).2)) z =
      (φ (treeParamFun X ζ θ z).1, φ (treeParamFun X ζ θ z).2) := by
  unfold treeParamFun; split_ifs
  · rfl
  · simp only [map_zero, Prod.fst_zero, Prod.snd_zero]; rfl

/-- **Tree node values are fixed integer combinations of the link parameters.** -/
theorem tree_node_linear (hX : X.DecodesTree G) (a : GNode G.tree) :
    ∃ A B : Fin (X.treeLinks (G.sig 0)).length → ℤ, ∀ (V : Type) [AddCommGroup V] (r : V)
      (θ : Fin (X.treeLinks (G.sig 0)).length → V × V),
      (treeDecOfParams hX r θ).1 a = r + ∑ j, (A j • (θ j).1 + B j • (θ j).2) := by
  refine ⟨fun j => chainVal (treeParamFun X (G.sig 0) (Pi.single j ((1 : ℤ), (0 : ℤ)))) X
      (G.sig 0) (0, []) 0 (fun _ => 0) a.1,
    fun j => chainVal (treeParamFun X (G.sig 0) (Pi.single j ((0 : ℤ), (1 : ℤ)))) X
      (G.sig 0) (0, []) 0 (fun _ => 0) a.1,
    fun V _ r θ => ?_⟩
  have ha := (tree_mem_nodes_iff hX a.1).1 a.2
  rw [Finset.mem_union, Finset.mem_singleton] at ha
  show chainVal (treeParamFun X (G.sig 0) θ) X (G.sig 0) (0, []) r (fun _ => r) a.1 = _
  have e1 := chainVal_add (treeParamFun X (G.sig 0) θ) 0 X (G.sig 0) ((0 : Fin 1), ([] : Path))
    0 r (fun _ => 0) (fun _ => r) a.1
  rw [add_zero, zero_add, fun_zero_add_const] at e1
  have hc : chainVal (0 : Fin 1 × Path → V × V) X (G.sig 0) (0, []) r (fun _ => r) a.1 = r := by
    refine chainVal_const X _ _ r a.1 ?_
    rcases ha with ha | ha
    · exact Or.inl ha
    · right; rw [ha]; exact lone_under X
  rw [e1, hc, add_comm]
  congr 1
  have hθ : θ = ∑ j : Fin (X.treeLinks (G.sig 0)).length,
      (Pi.single j ((θ j).1, 0) + Pi.single j (0, (θ j).2)) := by
    rw [← Finset.univ_sum_single θ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Pi.single_add]; simp
  have key : chainVal (treeParamFun X (G.sig 0) θ) X (G.sig 0) (0, []) 0 (fun _ => 0) a.1 =
      chainValHom X (G.sig 0) (0, []) a.1 (treeParamFunHom X (G.sig 0) θ) := rfl
  rw [key]
  conv_lhs => rw [hθ]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_add, map_add]
  have c1 := chainVal_map (zmultiplesHom V (θ j).1)
    (treeParamFun X (G.sig 0) (Pi.single j ((1 : ℤ), (0 : ℤ)))) X (G.sig 0) (0, []) 0
    (fun _ => 0) a.1
  have c2 := chainVal_map (zmultiplesHom V (θ j).2)
    (treeParamFun X (G.sig 0) (Pi.single j ((0 : ℤ), (1 : ℤ)))) X (G.sig 0) (0, []) 0
    (fun _ => 0) a.1
  have p1 : (fun x => ((zmultiplesHom V (θ j).1)
      (treeParamFun X (G.sig 0) (Pi.single j ((1 : ℤ), (0 : ℤ))) x).1,
      (zmultiplesHom V (θ j).1) (treeParamFun X (G.sig 0) (Pi.single j ((1 : ℤ), (0 : ℤ))) x).2)) =
      treeParamFunHom X (G.sig 0) (Pi.single j ((θ j).1, 0)) := by
    funext x
    rw [← treeParamFun_map]
    show treeParamFun X _ _ x = treeParamFun X _ _ x
    congr 1
    funext j'
    by_cases hj : j' = j
    · subst hj; simp [zmultiplesHom_apply]
    · simp [hj, zmultiplesHom_apply]
  have p2 : (fun x => ((zmultiplesHom V (θ j).2)
      (treeParamFun X (G.sig 0) (Pi.single j ((0 : ℤ), (1 : ℤ))) x).1,
      (zmultiplesHom V (θ j).2) (treeParamFun X (G.sig 0) (Pi.single j ((0 : ℤ), (1 : ℤ))) x).2)) =
      treeParamFunHom X (G.sig 0) (Pi.single j (0, (θ j).2)) := by
    funext x
    rw [← treeParamFun_map]
    show treeParamFun X _ _ x = treeParamFun X _ _ x
    congr 1
    funext j'
    by_cases hj : j' = j
    · subst hj; simp [zmultiplesHom_apply]
    · simp [hj, zmultiplesHom_apply]
  simp only [map_zero] at c1 c2
  rw [p1] at c1
  rw [p2] at c2
  show chainVal (treeParamFunHom X (G.sig 0) (Pi.single j ((θ j).1, 0))) X (G.sig 0) (0, []) 0
      (fun _ => 0) a.1 +
    chainVal (treeParamFunHom X (G.sig 0) (Pi.single j (0, (θ j).2))) X (G.sig 0) (0, []) 0
      (fun _ => 0) a.1 = _
  rw [← c1, ← c2]
  simp [zmultiplesHom_apply]

/-! ### Coordinates -/

/-- The paired leaves of sign `+`, as an index type. -/
abbrev TPlus (G : Garden 1) : Type := {ℓ : GLeaf G.tree // G.sign ℓ.toNode = 1 ∧ G.pair ℓ ≠ ℓ}

/-- The leaf coordinates of a tree: `none ↦ k_{ℓ_lo}`, `some ℓ ↦ k_ℓ` (`ℓ` paired, sign `+`). -/
abbrev TLeafCoord (G : Garden 1) : Type := Option (TPlus G)

/-- The link coordinates of a tree code: `none ↦ k`, `some (j, 0) ↦ x_j`, `some (j, 1) ↦ y_j`. -/
abbrev TLinkCoord (X : RegChain) (ζ : ℤˣ) : Type := Option (Fin (X.treeLinks ζ).length × Fin 2)

/-- The node of a leaf coordinate. -/
def leafNode (hX : X.DecodesTree G) : TLeafCoord G → GNode G.tree
  | none => (loneLeaf hX).toNode
  | some ℓ => ℓ.1.toNode

/-- The leaf coordinates of a decoration. -/
def treeLeafVals (hX : X.DecodesTree G) (κ : GNode G.tree → V) (o : TLeafCoord G) : V :=
  κ (leafNode hX o)

/-- The link coordinates `(k, x_j, y_j)` of a tree decoration. -/
def treeLinkCoords (X : RegChain) (κ : GNode G.tree → V) : TLinkCoord X (G.sig 0) → V
  | none => κ (GNode.root G.tree 0)
  | some (j, i) =>
    ![xv (extend κ) (treeChosen X (G.sig 0) j), yv (extend κ) (treeChosen X (G.sig 0) j)] i

theorem sum_plusPaired (f : GLeaf G.tree → V) :
    ∑ ℓ ∈ plusPaired G, f ℓ = ∑ ℓ : TPlus G, f ℓ.1 :=
  Finset.sum_subtype _ (fun ℓ => by simp [plusPaired]) f

/-- The value at any address is a fixed integer combination of the leaf coordinates. -/
theorem tree_exists_addr_expansion (hX : X.DecodesTree G) (x : Fin 1 × Path) :
    ∃ s : TLeafCoord G → ℤ, ∀ (V : Type) [AddCommGroup V] (κ : GNode G.tree → V),
      IsDecoration G κ → extend κ x = ∑ o, s o • treeLeafVals hX κ o := by
  by_cases hx : x.2 ∈ (G.tree x.1).nodes
  · obtain ⟨c, hc⟩ := exists_node_expansion (G := G) ⟨x, hx⟩
    refine ⟨fun o => match o with
      | none => c (loneLeaf hX)
      | some ℓ => c ℓ.1 + c (G.pair ℓ.1), fun V _ κ hκ => ?_⟩
    rw [show extend κ x = κ ⟨x, hx⟩ from extend_node κ ⟨x, hx⟩, hc V κ hκ,
      sum_fold_pairs_marked hκ, markedLeaves_eq hX, sum_singleton, sum_plusPaired,
      Fintype.sum_option, add_comm]
    rfl
  · refine ⟨0, fun V _ κ hκ => ?_⟩
    simp [extend, hx]

theorem card_gleaf {w : ℕ} (tree : Fin w → TTree) :
    Fintype.card (GLeaf tree) = ∑ j, (tree j).leaves.card := by
  rw [Fintype.card_eq_sum_ones]
  have : ∀ ℓ : GLeaf tree, (1 : ℕ) = ∑ j, if ℓ.1.1 = j then 1 else 0 := fun ℓ => by
    rw [Finset.sum_ite_eq]; simp
  rw [Finset.sum_congr rfl fun ℓ _ => this ℓ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.card_eq_sum_ones, sum_tree_leaves]

theorem card_tLeafCoord (hX : X.DecodesTree G) :
    Fintype.card (TLeafCoord G) = Fintype.card (TLinkCoord X (G.sig 0)) := by
  have h1 : Fintype.card (TPlus G) = (plusPaired G).card := by
    rw [Fintype.card_subtype]; rfl
  have h2 : ((Fintype.card (GLeaf G.tree) : ℕ) : ℤ) = 2 * (plusPaired G).card + 1 := by
    have h := sum_fold_pairs_marked (κ := fun _ : GNode G.tree => (1 : ℤ))
      ⟨fun _ => by norm_num, fun _ => rfl⟩ (fun _ => 1)
    rw [markedLeaves_eq hX] at h
    simp only [smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.card_singleton, Nat.cast_one] at h
    rw [h]; ring
  have h3 : Fintype.card (GLeaf G.tree) = 2 * X.size + 1 := by
    rw [card_gleaf, Fin.sum_univ_one, Comb.card_leaves, tree_eq_plug hX, code_plug_order,
      TTree.order, add_zero]
  have h4 : (X.treeLinks (G.sig 0)).length * 2 = X.size := chain_linksAt_length X _ _
  rw [h3] at h2
  rw [Fintype.card_option, Fintype.card_option, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, h1]
  omega

/-- **The unimodular change of variables for regular trees** (TARGET (incohproof1) for
`𝒦_𝒯^*`). For a tree carrier `G` decoded by `X` there are integer matrices `T` (leaf coordinates ×
link coordinates) and `S`, inverse to each other, with `k_o = ∑_i T o i u_i` and `u_i = ∑_o S i o k_o`
for every decoration in every additive group, where `k_o` are the leaf coordinates
(`treeLeafVals`: `k_{ℓ_lo}` and `k_ℓ` for the paired leaves of sign `+`) and `u` the link
coordinates (`treeLinkCoords`: `k, x_j, y_j`). Moreover `T o k = 1` (every `k_ℓ - k` is an integer
combination of the `(x_j, y_j)`) and the `k`-row of `S` reads `k = k_{ℓ_lo}`. -/
theorem tree_incoh_unimodular (hX : X.DecodesTree G) :
    ∃ (T : Matrix (TLeafCoord G) (TLinkCoord X (G.sig 0)) ℤ)
      (S : Matrix (TLinkCoord X (G.sig 0)) (TLeafCoord G) ℤ),
      T * S = 1 ∧ S * T = 1 ∧ (∀ o, T o none = 1) ∧ (∀ o, S none o = if o = none then 1 else 0) ∧
      ∀ (V : Type) [AddCommGroup V] (κ : GNode G.tree → V), IsDecoration G κ →
        (∀ o, treeLeafVals hX κ o = ∑ i, T o i • treeLinkCoords X κ i) ∧
        (∀ i, treeLinkCoords X κ i = ∑ o, S i o • treeLeafVals hX κ o) := by
  classical
  choose A B hAB using fun o : TLeafCoord G => tree_node_linear hX (leafNode hX o)
  let T : Matrix (TLeafCoord G) (TLinkCoord X (G.sig 0)) ℤ := fun o i =>
    match i with
    | none => 1
    | some (j, i) => ![A o j, B o j] i
  choose c hc using fun x : Fin 1 × Path => tree_exists_addr_expansion hX x
  let S : Matrix (TLinkCoord X (G.sig 0)) (TLeafCoord G) ℤ := fun i o =>
    match i with
    | none => if o = none then 1 else 0
    | some (j, i) =>
      ![c (addrExt (treeChosen X (G.sig 0) j) [0]) o - c (treeChosen X (G.sig 0) j) o,
        c (treeChosen X (G.sig 0) j) o - c (addrExt (treeChosen X (G.sig 0) j) [2]) o] i
  have hfwd : ∀ (V : Type) [AddCommGroup V] (κ : GNode G.tree → V), IsDecoration G κ →
      ∀ o, treeLeafVals hX κ o = ∑ i, T o i • treeLinkCoords X κ i := by
    intro V _ κ hκ o
    set r := κ (GNode.root G.tree 0)
    let κ' : DecRT G V r := ⟨κ, hκ, rfl⟩
    have hinv := (treeDecEquiv hX r).left_inv κ'
    have e1 : treeLeafVals hX κ o = (treeDecOfParams hX r (treeDecParams X κ')).1 (leafNode hX o) := by
      rw [show treeDecOfParams hX r (treeDecParams X κ') = κ' from hinv]; rfl
    rw [e1, hAB o V r (treeDecParams X κ'), Fintype.sum_option, Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two]
    simp only [T, treeLinkCoords, one_smul, Matrix.cons_val_zero, Matrix.cons_val_one,
      treeDecParams, κ']
    rfl
  have hbwd : ∀ (V : Type) [AddCommGroup V] (κ : GNode G.tree → V), IsDecoration G κ →
      ∀ i, treeLinkCoords X κ i = ∑ o, S i o • treeLeafVals hX κ o := by
    intro V _ κ hκ i
    rcases i with _ | ⟨j, i⟩
    · simp only [S, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte]
      exact tree_root_eq_lone hX hκ
    · rcases fin_two_cases i with rfl | rfl
      · show xv (extend κ) (treeChosen X (G.sig 0) j) = _
        rw [xv, hc _ V κ hκ, hc _ V κ hκ, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [← sub_smul]
        rfl
      · show yv (extend κ) (treeChosen X (G.sig 0) j) = _
        rw [yv, hc _ V κ hκ, hc _ V κ hκ, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [← sub_smul]
        rfl
  have hu_of : ∀ u : TLinkCoord X (G.sig 0) → ℤ, treeLinkCoords X
      (treeDecOfParams hX (u none) (fun j => (u (some (j, 0)), u (some (j, 1))))).1 = u := by
    intro u
    funext i''
    rcases i'' with _ | ⟨j, i''⟩
    · exact (treeDecOfParams hX (u none) _).2.2
    · have hp := congrFun (treeDecParams_treeDecOfParams hX (u none)
        (fun j => (u (some (j, 0)), u (some (j, 1))))) j
      rcases fin_two_cases i'' with rfl | rfl
      · exact congrArg Prod.fst hp
      · exact congrArg Prod.snd hp
  have hST : S * T = 1 := by
    ext i i'
    let u : TLinkCoord X (G.sig 0) → ℤ := fun i'' => if i'' = i' then 1 else 0
    let κ := treeDecOfParams hX (u none) (fun j => (u (some (j, 0)), u (some (j, 1))))
    have hu := hu_of u
    have h1 := hbwd ℤ κ.1 κ.2.1 i
    rw [hu] at h1
    have h2 : ∀ o : TLeafCoord G, treeLeafVals hX κ.1 o = T o i' := fun o => by
      rw [hfwd ℤ κ.1 κ.2.1 o, hu]
      simp only [u, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte]
    simp only [h2, smul_eq_mul] at h1
    rw [Matrix.mul_apply, Matrix.one_apply, ← h1]
  have hTS : T * S = 1 := by
    let e : TLeafCoord G ≃ TLinkCoord X (G.sig 0) := Fintype.equivOfCardEq (card_tLeafCoord hX)
    have key : (S.submatrix e id) * (T.submatrix id e) = 1 := by
      ext o o'
      have := congrFun (congrFun hST (e o)) (e o')
      simp only [Matrix.mul_apply, Matrix.submatrix_apply, id] at this ⊢
      rw [this]
      by_cases h : o = o'
      · subst h; simp
      · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (e.injective.ne h)]
    have key2 := mul_eq_one_comm.mp key
    ext o o'
    have := congrFun (congrFun key2 o) o'
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id] at this ⊢
    rw [← this]
    exact (Equiv.sum_comp e (fun i => T o i * S i o')).symm
  exact ⟨T, S, hTS, hST, fun _ => rfl, fun _ => rfl, fun V _ κ hκ => ⟨hfwd V κ hκ, hbwd V κ hκ⟩⟩

/-- Every link coordinate vector `(k, x_j, y_j)` is realized by a decoration of the tree. -/
theorem treeLinkCoords_surjective (hX : X.DecodesTree G) (u : TLinkCoord X (G.sig 0) → V) :
    ∃ κ : GNode G.tree → V, IsDecoration G κ ∧ treeLinkCoords X κ = u := by
  let κ := treeDecOfParams hX (u none) (fun j => (u (some (j, 0)), u (some (j, 1))))
  refine ⟨κ.1, κ.2.1, funext fun i => ?_⟩
  rcases i with _ | ⟨j, i⟩
  · exact κ.2.2
  · have hp := congrFun (treeDecParams_treeDecOfParams hX (u none)
      (fun j => (u (some (j, 0)), u (some (j, 1))))) j
    rcases fin_two_cases i with rfl | rfl
    · exact congrArg Prod.fst hp
    · exact congrArg Prod.snd hp

end WaveTurbulence.Links
