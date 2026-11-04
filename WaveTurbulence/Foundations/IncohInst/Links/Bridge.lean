/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Links.Partition
public import WaveTurbulence.Foundations.RegStruct.DecodedPairProperties

/-!
# Links on couple carriers (packet C2)

For a couple carrier `G` decoded by a code `Q` (B2 draft `RegCpl.Decodes`):

* `CplDec f Q a b` is equivalent to "node relations at the link endpoints and equal values on the
  decoded leaf pairs" (`cplDec_iff_lists`);
* a decoration `κ` of `G` (TARGET Def `defdec`) gives `CplDec (extend κ) Q (0,[]) (1,[])`
  (`cplDec_of_decoration`), and conversely (`isDecoration_of_cplDec`);
* hence every link `(𝔫, 𝔫')` of `Q.links` satisfies the link relation of TARGET Prop `deflink`
  for every decoration (`linkRel_of_decoration`).
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg Finset

variable {V : Type*} [AddCommGroup V] {w : ℕ}

/-! ### List form of `CplDec` -/

mutual
/-- Node relations at the link endpoints and equal values on the leaf pairs give `CplDec`. -/
theorem cplDec_of_lists (f : Fin w × Path → V) (Q : RegCpl) (a b : Fin w × Path)
    (hN : ∀ x ∈ pairEndpoints (Q.linksAt a b), NodeRel f x)
    (hP : ∀ p ∈ Q.pairsAt a b, f p.1 = f p.2) : CplDec f Q a b := by
  cases Q with
  | triv => exact hP (a, b) (by simp [RegCpl.pairsAt])
  | type1 c Q₁ Q₂ Q₃ =>
    simp only [RegCpl.linksAt, pairEndpoints_cons, pairEndpoints_append, Finset.mem_union,
      Finset.mem_singleton] at hN
    simp only [RegCpl.pairsAt, List.mem_append] at hP
    refine ⟨hN a (Or.inl rfl), hN b (Or.inr (Or.inl rfl)), ?_, ?_, ?_⟩
    · exact cplDec_of_lists f Q₁ _ _ (fun x hx => hN x (by tauto)) (fun p hp => hP p (by tauto))
    · exact cplDec_of_lists f Q₂ _ _ (fun x hx => hN x (by tauto)) (fun p hp => hP p (by tauto))
    · exact cplDec_of_lists f Q₃ _ _ (fun x hx => hN x (by tauto)) (fun p hp => hP p (by tauto))
  | type2 Xp Xm Qlp =>
    simp only [RegCpl.linksAt, pairEndpoints_append, Finset.mem_union] at hN
    simp only [RegCpl.pairsAt, List.mem_append] at hP
    refine ⟨?_, ?_, ?_⟩
    · exact chainDec_of_lists f Xp 1 a (fun x hx => hN x (by tauto)) (fun p hp => hP p (by tauto))
    · exact chainDec_of_lists f Xm (-1) b (fun x hx => hN x (by tauto))
        (fun p hp => hP p (by tauto))
    · exact cplDec_of_lists f Qlp _ _ (fun x hx => hN x (by tauto)) (fun p hp => hP p (by tauto))
termination_by structural Q

/-- Chain version of `cplDec_of_lists`. -/
theorem chainDec_of_lists (f : Fin w × Path → V) (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path)
    (hN : ∀ x ∈ pairEndpoints (X.linksAt ζ a), NodeRel f x)
    (hP : ∀ p ∈ X.pairsAt ζ a, f p.1 = f p.2) : ChainDec f X ζ a := by
  cases X with
  | nil => trivial
  | pair m Qr Qg inner rest =>
    simp only [RegChain.linksAt, pairEndpoints_cons, pairEndpoints_append, Finset.mem_union,
      Finset.mem_singleton] at hN
    simp only [RegChain.pairsAt, List.mem_append] at hP
    refine ⟨hN a (Or.inl rfl), hN _ (Or.inr (Or.inl rfl)), ?_, ?_, ?_, ?_⟩
    · split_ifs with hs <;> simp only [hs, ↓reduceIte] at hN hP <;>
        exact cplDec_of_lists f Qr _ _ (fun x hx => hN x (by tauto)) (fun p hp => hP p (by tauto))
    · split_ifs with hs <;> simp only [hs, ↓reduceIte] at hN hP <;>
        exact cplDec_of_lists f Qg _ _ (fun x hx => hN x (by tauto)) (fun p hp => hP p (by tauto))
    · exact chainDec_of_lists f inner _ _ (fun x hx => hN x (by tauto))
        (fun p hp => hP p (by tauto))
    · exact chainDec_of_lists f rest _ _ (fun x hx => hN x (by tauto))
        (fun p hp => hP p (by tauto))
termination_by structural X
end

mutual
/-- `CplDec` gives the node relations at all link endpoints. -/
theorem cplDec_nodeRel (f : Fin w × Path → V) (Q : RegCpl) (a b : Fin w × Path)
    (h : CplDec f Q a b) : ∀ x ∈ pairEndpoints (Q.linksAt a b), NodeRel f x := by
  cases Q with
  | triv => simp [RegCpl.linksAt]
  | type1 c Q₁ Q₂ Q₃ =>
    obtain ⟨ha, hb, h₁, h₂, h₃⟩ := h
    simp only [RegCpl.linksAt, pairEndpoints_cons, pairEndpoints_append, Finset.mem_union,
      Finset.mem_singleton]
    rintro x (rfl | rfl | ((hx | hx) | hx))
    · exact ha
    · exact hb
    · exact cplDec_nodeRel f Q₁ _ _ h₁ x hx
    · exact cplDec_nodeRel f Q₂ _ _ h₂ x hx
    · exact cplDec_nodeRel f Q₃ _ _ h₃ x hx
  | type2 Xp Xm Qlp =>
    obtain ⟨hp, hm, hl⟩ := h
    simp only [RegCpl.linksAt, pairEndpoints_append, Finset.mem_union]
    rintro x ((hx | hx) | hx)
    · exact chainDec_nodeRel f Xp _ _ hp x hx
    · exact chainDec_nodeRel f Xm _ _ hm x hx
    · exact cplDec_nodeRel f Qlp _ _ hl x hx
termination_by structural Q

/-- Chain version of `cplDec_nodeRel`. -/
theorem chainDec_nodeRel (f : Fin w × Path → V) (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path)
    (h : ChainDec f X ζ a) : ∀ x ∈ pairEndpoints (X.linksAt ζ a), NodeRel f x := by
  cases X with
  | nil => simp [RegChain.linksAt]
  | pair m Qr Qg inner rest =>
    obtain ⟨ha, hb, hr, hg, hi, hs⟩ := h
    simp only [RegChain.linksAt, pairEndpoints_cons, pairEndpoints_append, Finset.mem_union,
      Finset.mem_singleton]
    rintro x (rfl | rfl | (((hx | hx) | hx) | hx))
    · exact ha
    · exact hb
    · split_ifs at hr hx <;> exact cplDec_nodeRel f Qr _ _ hr x hx
    · split_ifs at hg hx <;> exact cplDec_nodeRel f Qg _ _ hg x hx
    · exact chainDec_nodeRel f inner _ _ hi x hx
    · exact chainDec_nodeRel f rest _ _ hs x hx
termination_by structural X
end

mutual
/-- `CplDec` gives equal values on all decoded leaf pairs. -/
theorem cplDec_pairs (f : Fin w × Path → V) (Q : RegCpl) (a b : Fin w × Path)
    (h : CplDec f Q a b) : ∀ p ∈ Q.pairsAt a b, f p.1 = f p.2 := by
  cases Q with
  | triv =>
    intro p hp
    simp only [RegCpl.pairsAt, List.mem_singleton] at hp
    subst hp
    exact h
  | type1 c Q₁ Q₂ Q₃ =>
    obtain ⟨-, -, h₁, h₂, h₃⟩ := h
    simp only [RegCpl.pairsAt, List.mem_append]
    rintro p ((hp | hp) | hp)
    · exact cplDec_pairs f Q₁ _ _ h₁ p hp
    · exact cplDec_pairs f Q₂ _ _ h₂ p hp
    · exact cplDec_pairs f Q₃ _ _ h₃ p hp
  | type2 Xp Xm Qlp =>
    obtain ⟨hp', hm, hl⟩ := h
    simp only [RegCpl.pairsAt, List.mem_append]
    rintro p ((hp | hp) | hp)
    · exact chainDec_pairs f Xp _ _ hp' p hp
    · exact chainDec_pairs f Xm _ _ hm p hp
    · exact cplDec_pairs f Qlp _ _ hl p hp
termination_by structural Q

/-- Chain version of `cplDec_pairs`. -/
theorem chainDec_pairs (f : Fin w × Path → V) (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path)
    (h : ChainDec f X ζ a) : ∀ p ∈ X.pairsAt ζ a, f p.1 = f p.2 := by
  cases X with
  | nil => simp [RegChain.pairsAt]
  | pair m Qr Qg inner rest =>
    obtain ⟨-, -, hr, hg, hi, hs⟩ := h
    simp only [RegChain.pairsAt, List.mem_append]
    rintro p (((hp | hp) | hp) | hp)
    · split_ifs at hr hp <;> exact cplDec_pairs f Qr _ _ hr p hp
    · split_ifs at hg hp <;> exact cplDec_pairs f Qg _ _ hg p hp
    · exact chainDec_pairs f inner _ _ hi p hp
    · exact chainDec_pairs f rest _ _ hs p hp
termination_by structural X
end

/-- **`CplDec` in list form.** -/
theorem cplDec_iff_lists (f : Fin w × Path → V) (Q : RegCpl) (a b : Fin w × Path) :
    CplDec f Q a b ↔ (∀ x ∈ pairEndpoints (Q.linksAt a b), NodeRel f x) ∧
      ∀ p ∈ Q.pairsAt a b, f p.1 = f p.2 :=
  ⟨fun h => ⟨cplDec_nodeRel f Q a b h, cplDec_pairs f Q a b h⟩,
    fun h => cplDec_of_lists f Q a b h.1 h.2⟩

/-! ### Carrier decorations -/

/-- A function on the nodes of a forest, extended by `0` to all global addresses. -/
def extend {tree : Fin w → TTree} (κ : GNode tree → V) (x : Fin w × Path) : V :=
  if h : x.2 ∈ (tree x.1).nodes then κ ⟨x, h⟩ else 0

theorem extend_node {tree : Fin w → TTree} (κ : GNode tree → V) (a : GNode tree) :
    extend κ a.1 = κ a := by
  unfold extend
  rw [dite_cond_eq_true (eq_true a.2)]
  rfl

theorem nodeRel_extend {G : Garden w} {κ : GNode G.tree → V} (hκ : IsDecoration G κ)
    (b : GBranch G.tree) : NodeRel (extend κ) b.1 := by
  have h := hκ.1 b
  unfold NodeRel
  have e : ∀ i : Fin 3, extend κ (addrExt b.1 [i]) = κ (b.child i) := fun i =>
    extend_node κ (b.child i)
  rw [e 0, e 1, e 2, ← h]
  exact extend_node κ b.toNode

/-- The forest of a decoded couple carrier is the decoded forest. -/
theorem tree_eq_coupleForest {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) :
    G.tree = coupleForest Q := by
  funext j
  fin_cases j
  · exact hQ.2.1
  · exact hQ.2.2.1

/-- On a decoded carrier, every decoded pair is a pair of the carrier. -/
theorem pair_of_decoded {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    {p : (Fin 2 × Path) × (Fin 2 × Path)} (hp : p ∈ Q.raw.2) :
    ∃ ℓ : GLeaf G.tree, ℓ.1 = p.1 ∧ (G.pair ℓ).1 = p.2 := by
  have hv := (decodedCouple_pairs_valid Q p hp).1
  rw [← tree_eq_coupleForest hQ] at hv
  refine ⟨⟨p.1, hv⟩, rfl, ?_⟩
  have h1 := hQ.2.2.2 ⟨p.1, hv⟩
  exact decodedPair_functional Q h1 (List.mem_append_left _ hp)

/-- **A decoration of a decoded couple carrier decorates the code.** -/
theorem cplDec_of_decoration {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    {κ : GNode G.tree → V} (hκ : IsDecoration G κ) : CplDec (extend κ) Q (0, []) (1, []) := by
  refine cplDec_of_lists _ Q _ _ ?_ ?_
  · intro x hx
    rw [← couple_branchAddresses] at hx
    have hb : x.2 ∈ (G.tree x.1).branching := by
      rw [tree_eq_coupleForest hQ]
      simp only [branchAddresses, Finset.mem_union, Finset.mem_image, addrExt] at hx
      rcases hx with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ <;> simpa [coupleForest] using hp
    exact nodeRel_extend hκ ⟨x, hb⟩
  · intro p hp
    obtain ⟨ℓ, h1, h2⟩ := pair_of_decoded hQ hp
    rw [← h1, ← h2]
    show extend κ ℓ.toNode.1 = extend κ (G.pair ℓ).toNode.1
    rw [extend_node, extend_node]
    exact hκ.2 ℓ

/-- **Conversely, a code decoration restricts to a decoration of the carrier.** -/
theorem isDecoration_of_cplDec {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    {f : Fin 2 × Path → V} (h : CplDec f Q (0, []) (1, [])) :
    IsDecoration G (fun a : GNode G.tree => f a.1) := by
  constructor
  · intro b
    obtain ⟨⟨j, p⟩, hbm⟩ := b
    have hb' : p ∈ (coupleForest Q j).branching := by
      rw [← tree_eq_coupleForest hQ]; exact hbm
    have hx : ((j, p) : Fin 2 × Path) ∈ pairEndpoints Q.links := by
      rw [RegCpl.links, ← couple_branchAddresses]
      fin_cases j <;> simp [branchAddresses, addrExt, coupleForest] at hb' ⊢ <;> exact hb'
    exact cplDec_nodeRel f Q _ _ h _ hx
  · intro ℓ
    have hm := hQ.2.2.2 ℓ
    have hp := cplDec_pairs f Q _ _ h
    rcases List.mem_append.mp hm with hm | hm
    · exact hp _ hm
    · obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hm
      have := hp q hq
      obtain ⟨q1, q2⟩ := q
      simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hqe
      obtain ⟨rfl, rfl⟩ := hqe
      exact this.symm

/-- **Links on carriers** (TARGET Prop `deflink`, DH21 Prop 4.3, FINDINGS F16): for every decoration
`κ` of a couple carrier `G` decoded by `Q`, every link of `Q` satisfies the link relation. -/
theorem linkRel_of_decoration {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
    {κ : GNode G.tree → V} (hκ : IsDecoration G κ) :
    ∀ l ∈ Q.links, LinkRel (extend κ) G.sig l.1 l.2 :=
  linkRel_of_cplDec _ _ Q _ _ (cplDec_of_decoration hQ hκ) (by simp [nodeSign, pathSign, hG.2])
    (by simp [nodeSign, pathSign, hG.2])

end WaveTurbulence.Links
