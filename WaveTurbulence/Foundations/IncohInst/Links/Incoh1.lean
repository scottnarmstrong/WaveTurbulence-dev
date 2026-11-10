/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Links.Linear
public import WaveTurbulence.Foundations.IncohInst.Links.Unique
public import WaveTurbulence.Foundations.IncohInst.Links.TreeLemmaOne
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The unimodular relation `incohproof1` (packet C2, for PL1)

TARGET proof of Prop 5.1, (incohproof1) (L985): for a regular couple of order `2n` with leaves `𝓛`,
the `2n+1` vectors `k_ℓ - k` (`ℓ ∈ 𝓛` of sign `+`) satisfy

  `∑_ℓ^{(+)} σ(ℓ) (k_ℓ - k) = 0`,  `σ(ℓ) ∈ {-1, 0, 1}`,  `∑ σ(ℓ) = ±1`,

and each `k_ℓ - k` is a fixed integer linear combination of `(x_𝔫, y_𝔫)_{𝔫 ∈ 𝒩^ch}` and vice versa,
giving an integer linear bijection between `(x, y)` and the subspace cut out by (incohproof1).

* `couple_roots_eq`: both roots of a couple decoration carry the same vector;
* `incoh_relation`, `incohSigma_sum`, `incohSigma_mem`: the relation with the explicit
  `σ(ℓ) = [ℓ ∈ 𝒯⁺] - [ℓ' ∈ 𝒯⁺]` (`ℓ'` the partner of `ℓ`), `∑ σ = 1`;
* `incoh_unimodular`: integer matrices `T : (+ leaves) × (k, x_j, y_j)` and `S` in the other
  direction with `T * S = 1`, `S * T = 1`, `T ℓ k = 1`, `S k = σ`, and
  `k_ℓ = ∑ T ℓ i u_i`, `u_i = ∑ S i ℓ k_ℓ` for every decoration in every additive group, where
  `u = (k, x_j, y_j)` are the link coordinates;
* `linkCoords_surjective`: every coordinate vector `u` comes from a decoration.

`epsXY_eq_cases` restates the Wick coefficient `ε` of a link in the three-case form used by the
`Incoh` link structure.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg Finset

variable {w : ℕ}

/-! ### Leaf expansions -/

/-- Sums over the leaves of one tree as sums over the leaves of the forest. -/
theorem sum_tree_leaves {M : Type*} [AddCommMonoid M] (tree : Fin w → TTree) (j : Fin w)
    (g : Path → M) :
    ∑ q ∈ (tree j).leaves, g q = ∑ ℓ : GLeaf tree, if ℓ.1.1 = j then g ℓ.1.2 else 0 := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij' (fun ℓ _ => ℓ.1.2) (fun q hq => (⟨(j, q), hq⟩ : GLeaf tree))
    ?_ ?_ ?_ ?_ ?_
  · intro ℓ hℓ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
    exact hℓ ▸ ℓ.2
  · intro q hq
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
  · intro ℓ hℓ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
    exact Subtype.ext (Prod.ext hℓ.symm rfl)
  · intro q hq; rfl
  · intro ℓ hℓ; rfl

variable {V : Type*} [AddCommGroup V]

/-- The root of tree `j` is the signed sum of its leaves. -/
theorem root_eq_sum_leaves {G : Garden w} {κ : GNode G.tree → V} (hκ : IsDecoration G κ)
    (j : Fin w) :
    κ (GNode.root G.tree j) =
      ∑ ℓ : GLeaf G.tree, (if ℓ.1.1 = j then (pathSign 1 ℓ.1.2 : ℤ) else 0) • κ ℓ.toNode := by
  have h : extend κ (GNode.root G.tree j).1 =
      ∑ q ∈ (G.tree j).leaves, (pathSign 1 q : ℤ) • extend κ (j, q) :=
    treeDec_root _ _ (treeDec_of_isDecoration hκ j)
  rw [extend_node, sum_tree_leaves] at h
  rw [h]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  split_ifs with hℓ
  · have e : (j, ℓ.1.2) = ℓ.toNode.1 := Prod.ext hℓ.symm rfl
    rw [e, extend_node]
  · simp

/-! ### Folding the pairing -/

/-- The leaves of sign `+`. -/
def plusLeaves (G : Garden w) : Finset (GLeaf G.tree) :=
  univ.filter fun ℓ => G.sign ℓ.toNode = 1

theorem pair_ne_of_plain {G : Garden w} (hP : G.IsPlain) (ℓ : GLeaf G.tree) : G.pair ℓ ≠ ℓ :=
  fun h => ((G.pair_eq_iff ℓ).1 h) (hP ℓ)

theorem sign_pair {G : Garden w} (hP : G.IsPlain) (ℓ : GLeaf G.tree) :
    G.sign (G.pair ℓ).toNode = -G.sign ℓ.toNode :=
  G.pair_sign ℓ (pair_ne_of_plain hP ℓ)

theorem mem_plusLeaves {G : Garden w} (ℓ : GLeaf G.tree) :
    ℓ ∈ plusLeaves G ↔ G.sign ℓ.toNode = 1 := by
  simp [plusLeaves]

/-- The pairing maps the leaves of sign `-` bijectively onto those of sign `+`. -/
theorem pair_mem_plus_iff {G : Garden w} (hP : G.IsPlain) (ℓ : GLeaf G.tree) :
    G.pair ℓ ∈ plusLeaves G ↔ ℓ ∉ plusLeaves G := by
  rw [mem_plusLeaves, mem_plusLeaves, sign_pair hP]
  rcases Int.units_eq_one_or (G.sign ℓ.toNode) with h | h <;> rw [h] <;> decide

/-- In a plain garden, a leaf sum folds onto the `+` leaves (`k_{ℓ'} = k_ℓ` on pairs). -/
theorem sum_fold_pairs {G : Garden w} (hP : G.IsPlain) {κ : GNode G.tree → V}
    (hκ : IsDecoration G κ) (f : GLeaf G.tree → ℤ) :
    ∑ ℓ, f ℓ • κ ℓ.toNode = ∑ ℓ ∈ plusLeaves G, (f ℓ + f (G.pair ℓ)) • κ ℓ.toNode := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun ℓ : GLeaf G.tree => G.sign ℓ.toNode = 1)]
  have h2 : ∑ ℓ ∈ univ.filter (fun ℓ : GLeaf G.tree => ¬ G.sign ℓ.toNode = 1), f ℓ • κ ℓ.toNode =
      ∑ ℓ ∈ plusLeaves G, f (G.pair ℓ) • κ ℓ.toNode := by
    refine Finset.sum_nbij' G.pair G.pair ?_ ?_ ?_ ?_ ?_
    · intro ℓ hℓ
      have hℓ' : ℓ ∉ plusLeaves G := by
        simpa [mem_plusLeaves] using hℓ
      simpa using (pair_mem_plus_iff hP ℓ).2 hℓ'
    · intro ℓ hℓ
      have hℓ' : ℓ ∈ plusLeaves G := by simpa using hℓ
      have := (pair_mem_plus_iff hP (G.pair ℓ)).1
      rw [G.pair_pair] at this
      have h3 : G.pair ℓ ∉ plusLeaves G := this hℓ'
      simpa [mem_plusLeaves] using h3
    · intro ℓ _; exact G.pair_pair ℓ
    · intro ℓ _; exact G.pair_pair ℓ
    · intro ℓ _
      rw [G.pair_pair, ← hκ.2 ℓ]
  rw [h2, plusLeaves, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ℓ _ => (add_smul _ _ _).symm

/-! ### Couples: equal roots and the relation (incohproof1) -/

variable {G : Garden 2}

theorem sign_of_tree0 (hG : IsCouple G) (ℓ : GLeaf G.tree) (h : ℓ.1.1 = 0) :
    ((pathSign 1 ℓ.1.2 : ℤˣ) : ℤ) = (G.sign ℓ.toNode : ℤ) := by
  show _ = ((pathSign (G.sig ℓ.1.1) ℓ.1.2 : ℤˣ) : ℤ)
  rw [h, hG.2]
  rfl

theorem fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  revert i; decide

/-- The coefficient `σ(ℓ) = [ℓ ∈ 𝒯⁺] - [ℓ' ∈ 𝒯⁺]` of (incohproof1), `ℓ'` the partner of `ℓ`. -/
def incohSigma (G : Garden 2) (ℓ : GLeaf G.tree) : ℤ :=
  (if ℓ.1.1 = 0 then 1 else 0) - (if (G.pair ℓ).1.1 = 0 then 1 else 0)

theorem incohSigma_mem (ℓ : GLeaf G.tree) : incohSigma G ℓ ∈ ({-1, 0, 1} : Finset ℤ) := by
  unfold incohSigma
  split_ifs <;> simp

/-- The root of `𝒯⁺` is the `σ`-combination of the `+` leaves. -/
theorem root_eq_sigma_sum (hG : IsCouple G) {κ : GNode G.tree → V} (hκ : IsDecoration G κ) :
    κ (GNode.root G.tree 0) = ∑ ℓ ∈ plusLeaves G, incohSigma G ℓ • κ ℓ.toNode := by
  rw [root_eq_sum_leaves hκ, sum_fold_pairs hG.1 hκ]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  rw [mem_plusLeaves] at hℓ
  have hp : G.sign (G.pair ℓ).toNode = -1 := by rw [sign_pair hG.1, hℓ]
  have key : ∀ ℓ' : GLeaf G.tree, (if ℓ'.1.1 = 0 then ((pathSign 1 ℓ'.1.2 : ℤˣ) : ℤ) else 0) =
      if ℓ'.1.1 = 0 then (G.sign ℓ'.toNode : ℤ) else 0 := fun ℓ' => by
    split_ifs with h
    · exact sign_of_tree0 hG ℓ' h
    · rfl
  congr 1
  rw [key ℓ, key (G.pair ℓ), hℓ, hp]
  unfold incohSigma
  split_ifs <;> simp

/-! ### The unimodular change of variables -/

/-- The `+` leaves, as an index type. -/
abbrev PlusLeaf (G : Garden 2) : Type := {ℓ : GLeaf G.tree // G.sign ℓ.toNode = 1}

/-- The link coordinates: `none ↦ k`, `some (j, 0) ↦ x_j`, `some (j, 1) ↦ y_j`. -/
abbrev LinkCoord (Q : RegCpl) : Type := Option (Fin Q.links.length × Fin 2)

/-- The link coordinates `(k, x_j, y_j)` of a decoration (`x, y` at the chosen nodes `𝒩^ch`). -/
def linkCoords (Q : RegCpl) (κ : GNode G.tree → V) : LinkCoord Q → V
  | none => κ (GNode.root G.tree 0)
  | some (j, i) => ![xv (extend κ) (chosenNode Q j), yv (extend κ) (chosenNode Q j)] i

theorem sum_plusLeaves (f : GLeaf G.tree → V) :
    ∑ ℓ ∈ plusLeaves G, f ℓ = ∑ ℓ : PlusLeaf G, f ℓ.1 :=
  Finset.sum_subtype _ (fun ℓ => mem_plusLeaves ℓ) f

theorem card_plusLeaf {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G) :
    Fintype.card (PlusLeaf G) = Fintype.card (LinkCoord Q) := by
  have h1 : Fintype.card (PlusLeaf G) = (plusLeaves G).card := Fintype.card_subtype _
  have h2 : (plusLeaves G).card * 2 = Fintype.card (GLeaf G.tree) := by
    have hneg : (univ.filter fun ℓ : GLeaf G.tree => ¬ G.sign ℓ.toNode = 1).card =
        (plusLeaves G).card := by
      refine Finset.card_nbij' G.pair G.pair ?_ ?_ ?_ ?_
      · intro ℓ hℓ
        have hℓ' : ℓ ∉ plusLeaves G := by simpa [mem_plusLeaves] using hℓ
        simpa using (pair_mem_plus_iff hG.1 ℓ).2 hℓ'
      · intro ℓ hℓ
        have hℓ' : ℓ ∈ plusLeaves G := by simpa using hℓ
        have := (pair_mem_plus_iff hG.1 (G.pair ℓ)).1
        rw [G.pair_pair] at this
        have h3 : G.pair ℓ ∉ plusLeaves G := this hℓ'
        simpa [mem_plusLeaves] using h3
      · intro ℓ _; exact G.pair_pair ℓ
      · intro ℓ _; exact G.pair_pair ℓ
    rw [← Finset.card_univ, ← Finset.card_filter_add_card_filter_not
      (s := univ) (fun ℓ : GLeaf G.tree => G.sign ℓ.toNode = 1), hneg, plusLeaves]
    ring
  have h3 : Fintype.card (GLeaf G.tree) = ∑ j, (G.tree j).leaves.card := by
    rw [Fintype.card_eq_sum_ones]
    have : ∀ ℓ : GLeaf G.tree, (1 : ℕ) = ∑ j, if ℓ.1.1 = j then 1 else 0 := fun ℓ => by
      rw [Finset.sum_ite_eq]; simp
    rw [Finset.sum_congr rfl fun ℓ _ => this ℓ, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.card_eq_sum_ones, sum_tree_leaves]
  have h4 : (G.tree 0).order + (G.tree 1).order = Q.size := by
    rw [tree_eq_coupleForest hQ]
    exact code_trees_order Q
  have h5 : Q.links.length * 2 = Q.size := couple_linksAt_length Q _ _
  rw [Fin.sum_univ_two, Comb.card_leaves, Comb.card_leaves] at h3
  rw [Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, h1]
  omega

/-- The Wick coefficient of a link in three-case form (`x = 0 ∧ y = 0 ↦ -1`, one of them zero
`↦ 0`, else `1`). -/
theorem epsXY_eq_cases {d : ℕ} (x y : Fin d → ℤ) :
    epsXY x y = if x = 0 ∧ y = 0 then -1 else if x = 0 ∨ y = 0 then 0 else 1 := by
  unfold epsXY
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]

/-! ### The Wick factor over the links -/

/-- The Wick coefficient `ε_{k_{𝔫₁} k_{𝔫₂} k_{𝔫₃}}` of one branching node. -/
def nodeEps {d : ℕ} (κ : GNode G.tree → (Fin d → ℤ)) (b : GBranch G.tree) : ℝ :=
  epsCoef (κ (b.child 0)) (κ (b.child 1)) (κ (b.child 2))

/-- The chosen node `𝔫_j ∈ 𝒩^ch` of the `j`-th link, as a branching node. -/
def chosenBranch {Q : RegCpl} (hQ : Q.Decodes G) (j : Fin Q.links.length) : GBranch G.tree :=
  ⟨chosenNode Q j, (link_branching hQ (List.get_mem _ _)).1⟩

theorem idxOf_chosenNode (Q : RegCpl) (j : Fin Q.links.length) :
    (Q.links.map Prod.fst).idxOf (chosenNode Q j) = j := by
  have := (chosen_nodup Q).idxOf_getElem j (by simp)
  simpa [chosenNode] using this

/-- **The Wick factor of a couple decoration factors over the links** (TARGET (incohproof2),
(incohproof9)): `ε_ℐ = ∏_{𝔫 ∈ 𝒩^ch} ε_𝔫²`, because `ε_{𝔫'} = ε_𝔫` on every link
(`epsCoef_link`). The per-link factor `ε_𝔫² = epsXY(x_𝔫, y_𝔫)²` equals `1`, `0`, `1` when `0`, `1`,
`2` of the vectors `x_𝔫, y_𝔫` vanish. -/
theorem epsDec_eq_prod_links {d : ℕ} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
    {κ : GNode G.tree → (Fin d → ℤ)} (hκ : IsDecoration G κ) :
    epsDec G κ = ∏ j : Fin Q.links.length,
      epsXY (xv (extend κ) (chosenNode Q j)) (yv (extend κ) (chosenNode Q j)) ^ 2 := by
  classical
  have hfxy : ∀ b, nodeEps κ b = epsXY (xv (extend κ) b.1) (yv (extend κ) b.1) := fun b => by
    rw [xv_extend, yv_extend]
    exact epsCoef_eq_epsXY _ _ _ _ (hκ.1 b)
  have hchosen : ∀ b : GBranch G.tree, b.1 ∈ chosenSet Q.links →
      nodeEps κ (linkPartner hQ b) = nodeEps κ b := fun b hb => by
    obtain ⟨hl, hbl⟩ := linkOf_spec hQ b
    have h1 : b.1 = (linkOf hQ b).1 := by
      rcases hbl with h | h
      · exact h
      · exact absurd (h ▸ hb) (chosenSet_link hQ hl).2
    exact epsCoef_link hQ hG hκ hl b (linkPartner hQ b) h1 (linkPartner_of_fst hQ hl b h1)
  have hsplit : epsDec G κ =
      ∏ b ∈ univ.filter (fun b : GBranch G.tree => b.1 ∈ chosenSet Q.links), nodeEps κ b ^ 2 := by
    change ∏ b, nodeEps κ b = _
    rw [← Finset.prod_filter_mul_prod_filter_not univ
      (fun b : GBranch G.tree => b.1 ∈ chosenSet Q.links)]
    have h2 : ∏ b ∈ univ.filter (fun b : GBranch G.tree => ¬ b.1 ∈ chosenSet Q.links), nodeEps κ b =
        ∏ b ∈ univ.filter (fun b : GBranch G.tree => b.1 ∈ chosenSet Q.links), nodeEps κ b := by
      refine Finset.prod_nbij' (linkPartner hQ) (linkPartner hQ) ?_ ?_ ?_ ?_ ?_
      · intro b hb
        have hb' : b.1 ∉ chosenSet Q.links := by simpa using hb
        rcases chosen_xor hQ b with h | h
        · exact absurd h.1 hb'
        · simpa using h.2
      · intro b hb
        have hb' : b.1 ∈ chosenSet Q.links := by simpa using hb
        rcases chosen_xor hQ b with h | h
        · simpa using h.2
        · exact absurd hb' h.1
      · intro b _; exact linkPartner_linkPartner hQ b
      · intro b _; exact linkPartner_linkPartner hQ b
      · intro b hb
        simp only [mem_filter, mem_univ, true_and] at hb
        have hp : (linkPartner hQ b).1 ∈ chosenSet Q.links := by
          rcases chosen_xor hQ b with h | h
          · exact absurd h.1 hb
          · exact h.2
        have := hchosen _ hp
        rw [linkPartner_linkPartner] at this
        exact this
    rw [h2, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun b _ => (sq _).symm
  rw [hsplit]
  symm
  refine Finset.prod_bij (fun j _ => chosenBranch hQ j) ?_ ?_ ?_ ?_
  · intro j _
    simp only [mem_filter, mem_univ, true_and]
    exact List.mem_toFinset.2 (List.mem_map_of_mem (List.get_mem _ _))
  · intro j₁ _ j₂ _ h
    have h' : chosenNode Q j₁ = chosenNode Q j₂ := congrArg Subtype.val h
    clear h
    exact Fin.ext (by rw [← idxOf_chosenNode Q j₁, ← idxOf_chosenNode Q j₂, h'])
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    have hm : b.1 ∈ Q.links.map Prod.fst := List.mem_toFinset.1 hb
    have hlt : (Q.links.map Prod.fst).idxOf b.1 < Q.links.length := by
      simpa using List.idxOf_lt_length_of_mem hm
    refine ⟨⟨_, hlt⟩, mem_univ _, Subtype.ext ?_⟩
    have := List.getElem_idxOf (List.idxOf_lt_length_of_mem hm)
    rw [List.getElem_map] at this
    show (Q.links.get ⟨_, hlt⟩).1 = b.1
    rw [List.get_eq_getElem]
    exact this
  · intro j _
    rw [hfxy]
    rfl

end WaveTurbulence.Links
