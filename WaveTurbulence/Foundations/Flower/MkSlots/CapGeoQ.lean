/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.CapD3
public import WaveTurbulence.Foundations.Flower.MkSlots.CapConv
public import WaveTurbulence.Foundations.Flower.MkSlots.IntCapHyp

/-! # B3s MK-SLOTS (cap slots): the geometry of a cap pair slot

For a cap pair `q` of the skeleton of a reconstruction (one leaf in a cap tree `J`, cap trees single leaves), the
native couple code `Q = D.couple q` (embedded at the two inflated leaf positions, main's
`LFTwist.reconstruction_coupleEmb`) is
* trivial-shaped (both trees leaves), or
* `type2 X nil triv` (cap at the second leaf) or `type2 nil X triv` (cap at the first leaf), `X ≠ nil`
(`capSlot_cases`, via D2b's `code_of_trees*_leaf`). In the second case the native couple is a D6b cap couple
(`capG_left`, `capG_right`), the chain `X` is a D2b stem chain of the reconstruction (`capStem`), and its paired
tree is D2b's `objTree` of the reconstruction (`capT1_eq`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.Links WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.ProtWhole
  WaveTurbulence.Flower.MkDefs

namespace WaveTurbulence.Flower.MkSlots

theorem leaf_subtreeAt (p : Path) : TTree.leaf.subtreeAt p = .leaf := by
  cases p <;> rfl

theorem plug_nil_ne_leaf {X : RegChain} (ζ : ℤˣ) (h : X.plug ζ .leaf ≠ .leaf) : X ≠ .nil := by
  rintro rfl
  exact h rfl

/-! ### The code of a cap pair -/

section Code

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)

/-- The attachment address of the first leaf of a source pair. -/
abbrev capUA (q : SourcePair S) : Fin w × Path := inflatedPosition S D.tree (q.firstLeaf hS).toNode

/-- The attachment address of the second leaf of a source pair. -/
abbrev capUB (q : SourcePair S) : Fin w × Path := inflatedPosition S D.tree (q.secondLeaf hS).toNode

theorem capCouple_emb (q : SourcePair S) :
    Embeds (D.garden hS) (D.couple q) (capUA D hS q) (capUB D hS q) :=
  LFTwist.reconstruction_coupleEmb D hS (D.garden_decodes hS) q

theorem capUA_fst (q : SourcePair S) : (capUA D hS q).1 = (q.firstLeaf hS).1.1 :=
  inflatedPosition_index S D.tree _

theorem capUB_fst (q : SourcePair S) : (capUB D hS q).1 = (q.secondLeaf hS).1.1 :=
  inflatedPosition_index S D.tree _

/-- **The code of a cap pair.** -/
theorem capSlot_cases (J : Finset (Fin w)) (hcap : ∀ j ∈ J, (D.garden hS).tree j = .leaf) (q : SourcePair S)
    (hq : IsCapPair S hS J q) :
    ((D.couple q).trees.1 = .leaf ∧ (D.couple q).trees.2 = .leaf) ∨
    (∃ X : RegChain, X.wf = true ∧ X ≠ .nil ∧ D.couple q = .type2 X .nil .triv ∧
      (q.secondLeaf hS).1.1 ∈ J ∧ (q.firstLeaf hS).1.1 ∉ J) ∨
    (∃ X : RegChain, X.wf = true ∧ X ≠ .nil ∧ D.couple q = .type2 .nil X .triv ∧
      (q.firstLeaf hS).1.1 ∈ J ∧ (q.secondLeaf hS).1.1 ∉ J) := by
  have hE := capCouple_emb D hS q
  have hwf := D.couple_wf q
  have h1J : (q.firstLeaf hS).1.1 ∈ J → (D.couple q).trees.1 = .leaf := by
    intro hj
    rw [← hE.treeA, capUA_fst, hcap _ hj, leaf_subtreeAt]
  have h2J : (q.secondLeaf hS).1.1 ∈ J → (D.couple q).trees.2 = .leaf := by
    intro hj
    rw [← hE.treeB, capUB_fst, hcap _ hj, leaf_subtreeAt]
  by_cases ht1 : (D.couple q).trees.1 = .leaf
  · by_cases ht2 : (D.couple q).trees.2 = .leaf
    · exact Or.inl ⟨ht1, ht2⟩
    · obtain ⟨X, hQ, hX⟩ := code_of_trees1_leaf hwf ht1 ht2
      have h2 : (q.secondLeaf hS).1.1 ∉ J := fun h => ht2 (h2J h)
      have h1 : (q.firstLeaf hS).1.1 ∈ J := hq.resolve_right h2
      refine Or.inr (Or.inr ⟨X, hX, ?_, hQ, h1, h2⟩)
      refine plug_nil_ne_leaf (-1) ?_
      have := ht2
      rw [hQ] at this
      exact this
  · by_cases ht2 : (D.couple q).trees.2 = .leaf
    · obtain ⟨X, hQ, hX⟩ := code_of_trees2_leaf hwf ht2 ht1
      have h1 : (q.firstLeaf hS).1.1 ∉ J := fun h => ht1 (h1J h)
      have h2 : (q.secondLeaf hS).1.1 ∈ J := hq.resolve_left h1
      refine Or.inr (Or.inl ⟨X, hX, ?_, hQ, h2, h1⟩)
      refine plug_nil_ne_leaf 1 ?_
      have := ht1
      rw [hQ] at this
      exact this
    · rcases hq with h | h
      · exact absurd (h1J h) ht1
      · exact absurd (h2J h) ht2

end Code

/-! ### The native couple is a D6b cap couple -/

theorem capG_left {LG : LayeredGarden 2} {X : RegChain} (hg : LG.garden = decodedCouple (.type2 X .nil .triv)) :
    CapG LG 0 1 X 1 := by
  obtain ⟨G, lay, hl⟩ := LG
  simp only at hg
  subst hg
  have hdec := decodedCouple_decodes (.type2 X .nil .triv)
  obtain ⟨hC, hN, hlp⟩ := (Embeds.of_decodes hdec).type2
  refine ⟨by decide, hC, ?_, ?_, fun ℓ hℓ => ?_, hdec.1.1⟩
  · have := hN.tree
    rw [show ((1 : Fin 2), ([] : Path)).2 = [] from rfl] at this
    exact this
  · rw [hdec.1.2]; rfl
  · have := hlp.pairs _ (List.mem_singleton_self _) ℓ (by rw [hℓ]; simp [addrExt])
    rw [this]
    simp [addrExt, RegChain.lonePath]

theorem capG_right {LG : LayeredGarden 2} {X : RegChain} (hg : LG.garden = decodedCouple (.type2 .nil X .triv)) :
    CapG LG 1 0 X (-1) := by
  obtain ⟨G, lay, hl⟩ := LG
  simp only at hg
  subst hg
  have hdec := decodedCouple_decodes (.type2 .nil X .triv)
  obtain ⟨hN, hC, hlp⟩ := (Embeds.of_decodes hdec).type2
  refine ⟨by decide, hC, ?_, ?_, fun ℓ hℓ => ?_, hdec.1.1⟩
  · exact hN.tree
  · rw [hdec.1.2]; rfl
  · -- the cap leaf at `(0, [])` is paired with the lone leaf at `(1, X.lonePath)`
    have hcap : ([] : Path) ∈ ((decodedCouple (.type2 .nil X .triv)).tree 0).leaves := by
      have := hN.tree
      simp only at this
      rw [show (decodedCouple (.type2 .nil X .triv)).tree 0 = TTree.leaf from this]
      simp [TTree.leaves]
    let g : GLeaf (decodedCouple (.type2 .nil X .triv)).tree := ⟨((0 : Fin 2), []), hcap⟩
    have e := hlp.pairs _ (List.mem_singleton_self _) g (by simp [g, addrExt, RegChain.lonePath])
    have hg : (decodedCouple (.type2 .nil X .triv)).pair g = ℓ := Subtype.ext (e.trans (by
      rw [hℓ]; simp [addrExt]))
    rw [← hg, (decodedCouple (.type2 .nil X .triv)).pair_pair]

theorem two_le_lonePath {X : RegChain} (hX : X ≠ .nil) : 2 ≤ X.lonePath.length := by
  cases X with
  | nil => exact absurd rfl hX
  | pair m Qr Qg inner rest => simp [RegChain.lonePath]; omega

theorem lonePath_ne_nil {X : RegChain} (hX : X ≠ .nil) : X.lonePath ≠ [] := by
  intro h
  have := two_le_lonePath hX
  rw [h] at this
  simp at this

theorem dropLast_lonePath_ne {X : RegChain} (hX : X ≠ .nil) : X.lonePath.dropLast ≠ X.lonePath := by
  intro h
  have := congrArg List.length h
  rw [List.length_dropLast] at this
  have := two_le_lonePath hX
  omega

/-! ### The data of a nontrivial cap slot -/

/-- **A nontrivial cap slot**: the chain side `j0` (skeleton leaf `leaf`), the cap side `c` (skeleton leaf
`cleaf`, in a cap tree), the chain code `X ≠ nil` with its sign `ζ`, and their embedding in the reconstruction. -/
structure CapSide {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (J : Finset (Fin w))
    (q : SourcePair S) where
  j0 : Fin 2
  c : Fin 2
  X : RegChain
  ζ : ℤˣ
  leaf : GLeaf S.tree
  cleaf : GLeaf S.tree
  wf : X.wf = true
  ne : X ≠ .nil
  capG : ∀ LG : LayeredGarden 2, LG.garden = decodedCouple (D.couple q) → CapG LG j0 c X ζ
  root_j0 : (nativeCoupleForest D hS q).root j0 = attachedNode D hS leaf.toNode
  root_c : (nativeCoupleForest D hS q).root c = attachedNode D hS cleaf.toNode
  arg : Represents.argSrc hS (.inl q) j0 = Represents.clkOfNode S leaf.toNode
  emb : ChainEmb (D.garden hS) X ζ (inflatedPosition S D.tree leaf.toNode) .leaf
  lone : ∀ ℓ : GLeaf (D.garden hS).tree, ℓ.1 = addrExt (inflatedPosition S D.tree leaf.toNode) X.lonePath →
    ((D.garden hS).pair ℓ).1 = inflatedPosition S D.tree cleaf.toNode
  cJ : cleaf.1.1 ∈ J
  lJ : leaf.1.1 ∉ J
  sign : nodeSign S.sig leaf.1 = ζ
  links : (D.couple q).links = X.linksAt ζ (j0, [])
  size : (D.couple q).size = X.size
  capTree : capTreeOf S hS J q = cleaf.1.1

section Side

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)

/-- The cap at the second leaf. -/
def capSideLeft (J : Finset (Fin w)) (q : SourcePair S) (X : RegChain) (hX : X.wf = true) (hne : X ≠ .nil)
    (hQ : D.couple q = .type2 X .nil .triv) (h2 : (q.secondLeaf hS).1.1 ∈ J) (h1 : (q.firstLeaf hS).1.1 ∉ J) :
    CapSide D hS J q where
  j0 := 0
  c := 1
  X := X
  ζ := 1
  leaf := q.firstLeaf hS
  cleaf := q.secondLeaf hS
  wf := hX
  ne := hne
  capG := fun LG hg => capG_left (hg.trans (by rw [hQ]))
  root_j0 := rfl
  root_c := rfl
  arg := by simp [Represents.argSrc]
  emb := by
    have hE := capCouple_emb D hS q
    rw [hQ] at hE
    exact hE.type2.1
  lone := by
    intro ℓ hℓ
    have hE := capCouple_emb D hS q
    rw [hQ] at hE
    have := hE.type2.2.2.pairs _ (List.mem_singleton_self _) ℓ hℓ
    rw [this]
    simp [addrExt, RegChain.lonePath]
  cJ := h2
  lJ := h1
  sign := sourcePair_first_sign S hS q
  links := by rw [hQ]; simp [RegCpl.links, RegCpl.linksAt, RegChain.linksAt]
  size := by rw [hQ]; simp [RegCpl.size, RegChain.size]
  capTree := by simp [capTreeOf, h1]

/-- The cap at the first leaf. -/
def capSideRight (J : Finset (Fin w)) (hcap : ∀ j ∈ J, (D.garden hS).tree j = .leaf) (q : SourcePair S)
    (X : RegChain) (hX : X.wf = true) (hne : X ≠ .nil)
    (hQ : D.couple q = .type2 .nil X .triv) (h1 : (q.firstLeaf hS).1.1 ∈ J) (h2 : (q.secondLeaf hS).1.1 ∉ J) :
    CapSide D hS J q where
  j0 := 1
  c := 0
  X := X
  ζ := -1
  leaf := q.secondLeaf hS
  cleaf := q.firstLeaf hS
  wf := hX
  ne := hne
  capG := fun LG hg => capG_right (hg.trans (by rw [hQ]))
  root_j0 := rfl
  root_c := rfl
  arg := by simp [Represents.argSrc]
  emb := by
    have hE := capCouple_emb D hS q
    rw [hQ] at hE
    exact hE.type2.2.1
  lone := by
    intro ℓ hℓ
    have hE := capCouple_emb D hS q
    have hA := hE.nodeA
    rw [hQ] at hE
    have hleaf : (capUA D hS q).2 ∈ ((D.garden hS).tree (capUA D hS q).1).leaves := by
      have ht : (D.garden hS).tree (capUA D hS q).1 = .leaf := by rw [capUA_fst]; exact hcap _ h1
      rw [ht] at hA ⊢
      exact hA
    let g : GLeaf (D.garden hS).tree := ⟨capUA D hS q, hleaf⟩
    have e := hE.type2.2.2.pairs _ (List.mem_singleton_self _) g (by simp [g, addrExt, RegChain.lonePath])
    have hg : (D.garden hS).pair g = ℓ := Subtype.ext (e.trans hℓ.symm)
    rw [← hg, (D.garden hS).pair_pair]
  cJ := h1
  lJ := h2
  sign := sourcePair_second_sign S hS q
  links := by rw [hQ]; simp [RegCpl.links, RegCpl.linksAt, RegChain.linksAt]
  size := by rw [hQ]; simp [RegCpl.size, RegChain.size]
  capTree := by simp [capTreeOf, h1]

end Side

end WaveTurbulence.Flower.MkSlots
