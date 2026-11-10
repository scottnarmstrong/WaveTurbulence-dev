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

end WaveTurbulence.Links
