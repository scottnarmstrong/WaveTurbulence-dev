/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.Mem
public import WaveTurbulence.Foundations.VineEst.VineEstS4.AbsMeas
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.GateH
public import WaveTurbulence.Foundations.Spine.InputLeafCount
public import WaveTurbulence.Foundations.RegStruct.DecodedTreeProperties

/-! # P4-W2 AUX (d): the leaf-cost identity of the exceptional pair

The number of input leaves of a garden (`inputLeaves`: sign `+`, unmarked) is `order + w/2`-ish: `2 |in| + |marked| = 2 order + w`
(`card_inputLeaves_add_marked`).  For a plain couple (`w = 2`, no marked leaf) `|in| = order + 1`; for a paired tree (`w = 1`, one marked leaf)
`|in| = order`.  The carrier-side exceptional couple and tree `zpObjC b`, `zpObjT b` of a bundle member `b` and the native ones
(`sigStar A pstar`, i.e. `nativeCoupleLayered` at the pair `p₀` and `nativeChainLayered` at the lower branch) both have total order `2 zpN` (by
`zp_half_sizes`), hence the same total number of input leaves `2 zpN + 1` and, for a constant layer bound, the same leaf cost `B₀^{2 zpN + 1}`. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj WaveTurbulence.Reg.Skeleton
  WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P4.W13 TTree Finset

/-- **Leaf count of any garden**: `2 |inputLeaves| + |marked leaves| = 2 order + w`. -/
theorem card_inputLeaves_add_marked {w : ℕ} (G : Garden w) :
    2 * (inputLeaves G).card + (univ.filter fun l : GLeaf G.tree => G.mark l ≠ none).card = 2 * G.order + w := by
  classical
  let P : Finset (GLeaf G.tree) := univ.filter fun l => G.mark l = none
  let S := P.filter fun l => G.sign l.toNode = 1
  let T := P.filter fun l => ¬ G.sign l.toNode = 1
  have hmk : ∀ l, G.mark l = none ↔ G.pair l ≠ l := fun l => by
    have := G.pair_eq_iff l
    constructor
    · intro h he; exact (this.1 he) h
    · intro h; by_contra hm; exact h (this.2 hm)
  have hflip (l : GLeaf G.tree) (hl : G.mark l = none) : G.sign (G.pair l).toNode = -G.sign l.toNode :=
    G.pair_sign l ((hmk l).1 hl)
  have hmk' (l : GLeaf G.tree) (hl : G.mark l = none) : G.mark (G.pair l) = none := by
    rw [hmk]
    intro he
    have h1 := (hmk l).1 hl
    apply h1
    rw [G.pair_pair] at he
    exact he.symm
  have hst : S.card = T.card := by
    apply card_bij (fun l _ => G.pair l)
    · intro l hl
      obtain ⟨hlP, hs⟩ := mem_filter.mp hl
      have hl0 : G.mark l = none := (mem_filter.mp hlP).2
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hmk' l hl0⟩, ?_⟩
      rw [hflip l hl0, hs]
      decide
    · intro a _ b _ he
      have hh := congrArg G.pair he
      simpa only [G.pair_pair] using hh
    · intro l hl
      obtain ⟨hlP, hs⟩ := mem_filter.mp hl
      have hl0 : G.mark l = none := (mem_filter.mp hlP).2
      have hs' : G.sign l.toNode = -1 := (Int.units_eq_one_or _).resolve_left hs
      refine ⟨G.pair l, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hmk' l hl0⟩, ?_⟩, G.pair_pair l⟩
      rw [hflip l hl0, hs', neg_neg]
  have hinput : inputLeaves G = S := by
    ext l
    simp only [inputLeaves, S, P, mem_filter, mem_univ, true_and]
    tauto
  have hP : S.card + T.card = P.card := card_filter_add_card_filter_not _
  have hc := card_filter_add_card_filter_not (s := (univ : Finset (GLeaf G.tree))) (fun l => G.mark l = none)
  rw [card_univ, Comb.card_gleaf] at hc
  change P.card + (univ.filter fun l : GLeaf G.tree => ¬ G.mark l = none).card = 2 * G.order + w at hc
  rw [hinput]
  have e : (univ.filter fun l : GLeaf G.tree => G.mark l ≠ none) = (univ.filter fun l : GLeaf G.tree => ¬ G.mark l = none) := rfl
  rw [e]
  omega

/-- A plain couple has `order + 1` input leaves. -/
theorem card_inputLeaves_plain_couple (G : Garden 2) (hp : G.IsPlain) : (inputLeaves G).card = G.order + 1 := by
  have h := card_inputLeaves_add_marked G
  have h0 : (univ.filter fun l : GLeaf G.tree => G.mark l ≠ none).card = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro l _
    exact not_not.2 (hp l)
  omega

/-- A paired tree has `order` input leaves. -/
theorem card_inputLeaves_paired_tree (G : Garden 1) (hp : IsPairedTree G) : (inputLeaves G).card = G.order := by
  have h := card_inputLeaves_add_marked G
  rw [hp.1] at h
  omega

/-- The order of a garden decoding a chain code is the size of the code. -/
theorem decodesTree_order' {X : RegChain} {G : Garden 1} (hX : X.DecodesTree G) : G.order = X.size := by
  have h : G.order = (X.plug (G.sig 0) .leaf).order := by
    unfold Garden.order
    rw [Fin.sum_univ_one, hX.1]
  rw [h]
  simp only [code_plug_order, TTree.order, Nat.add_zero]

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι]

variable (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton)
  (hcan : CanonicalObject p kind A.layered)
  (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement pstar) (A.family.kind pstar)
    (A.family.atoms pstar) (A.family.upper pstar))
  (htc : CohOn A.layered ((A.data.tree (A.family.placement pstar).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement pstar).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement pstar).lower.toNode)))
  (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).secondLeaf A.plain).toNode)))

include hcan hel htc hcc in
/-- **Leaf count of the carrier-side exceptional pair of a bundle member**: `2 zpN + 1` input leaves in total. -/
theorem zp_leafCard (b : ST w ι pstar J) (hb : b ∈ zpFinset p kind pstar J A sp0 hA) :
    (inputLeaves (zpObjC b.1 pstar).garden).card + (inputLeaves (zpObjT b.1 pstar).garden).card = 2 * zpN A pstar + 1 := by
  have hc := nat_cohC A sp0 hA hcan hel htc hcc b hb
  have ht := nat_cohT A sp0 hA hcan hel htc hcc b hb
  rw [card_inputLeaves_plain_couple _ hc.2.1.1.1, card_inputLeaves_paired_tree _ (isPairedTree_of_decodesTree ht.2.1)]
  have h1 := RegCpl.size_eq_order _ hc.2.1
  have h2 := decodesTree_order' ht.2.1
  have := zp_sizes A sp0 hA hcan hel htc hcc b hb
  omega

omit hcan hel htc hcc in
/-- **Leaf count of the native exceptional pair** (`sigStar A pstar`: the native couple at the pair `p₀`, the native tree at the lower branch):
`2 zpN + 1` input leaves in total. -/
theorem native_leafCard :
    (inputLeaves (sigStar A pstar).2.1.garden).card + (inputLeaves (sigStar A pstar).2.2.garden).card = 2 * zpN A pstar + 1 := by
  have hpl : (sigStar A pstar).2.1.garden.IsPlain := native_couple_plain A.data A.plain (stateLayer A) (stateLayer_isLayering A) _
  have hpt : IsPairedTree (sigStar A pstar).2.2.garden := native_chain_paired A.data A.plain (stateLayer A) (stateLayer_isLayering A) _
  rw [card_inputLeaves_plain_couple _ hpl, card_inputLeaves_paired_tree _ hpt]
  have h1 : (sigStar A pstar).2.1.garden.order = (A.data.couple (pairOfLeaf A.skeleton A.plain
      (A.family.placement pstar).retained)).size := by
    change (nativeCoupleLayered _ _ _ _ _).garden.order = _
    rw [nativeCoupleLayered_garden]; exact decodedCouple_order _
  have h2 : (sigStar A pstar).2.2.garden.order = (A.data.tree (A.family.placement pstar).lower).size := by
    change (decodedTree _ _).order = _
    exact decodedTree_order _ _
  have := ZpSurj.two_zpN A (pstar := pstar)
  omega

/-- The leaf cost with a constant layer bound is a power of the number of input leaves. -/
theorem layerCost_const {w : ℕ} (B0 : ℝ) (LG : LayeredGarden w) :
    layerCost (fun _ => B0) LG = B0 ^ (inputLeaves LG.garden).card := by
  unfold layerCost
  rw [Finset.prod_const]

end WaveTurbulence.VineEstS5C.P4.W2
