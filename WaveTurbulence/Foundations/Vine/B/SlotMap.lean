/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.PStar
import Mathlib.Tactic

/-!
# VINE-B: the slots of `G_sb` are the outer slots of the skeleton

`iota : ReplacementSlot G_sb → ReplacementSlot S` (a leaf pair of `G_sb` goes to the pair of its image leaves, a branch
to its image branch) is a bijection onto `outerSlots` (`iota_bijOn`), with the same slot momentum node
(`node_slotNode`).  Its clock sources are those of `G_sb` (`srcMap`) except at a lower joint `u2^j`
(`argSrc_iota`); `route` sends those clocks to the unit (S2's `outerValM` routing, natural by construction).
`hclk`, `hmom`: the exterior clocks and the four boundary nodes of a unit, as `G_sb` data.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S}
  {Gsb : Garden w}

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

theorem leaf_sign (ℓ : GLeaf Gsb.tree) : nodeSign S.sig (Φ.leaf ℓ).1 = nodeSign Gsb.sig ℓ.1 := by
  have h := Φ.sign ℓ.toNode
  rw [← Φ.leaf_node] at h
  exact h

/-- The slot embedding. -/
noncomputable def iota (hS : S.IsPlain) (hSb : Gsb.IsPlain) : ReplacementSlot Gsb → ReplacementSlot S
  | .inl p => .inl (pairOfLeaf S hS (Φ.leaf (p.firstLeaf hSb)))
  | .inr c => .inr (Φ.br c)

theorem iota_first (hS : S.IsPlain) (hSb : Gsb.IsPlain) (p : SourcePair Gsb) :
    (pairOfLeaf S hS (Φ.leaf (p.firstLeaf hSb))).firstLeaf hS = Φ.leaf (p.firstLeaf hSb) :=
  pairOfLeaf_first_of_positive S hS _ ((Φ.leaf_sign _).trans (sourcePair_first_sign Gsb hSb p))

theorem iota_second (hS : S.IsPlain) (hSb : Gsb.IsPlain) (p : SourcePair Gsb) :
    (pairOfLeaf S hS (Φ.leaf (p.firstLeaf hSb))).secondLeaf hS = Φ.leaf (p.secondLeaf hSb) := by
  set q := pairOfLeaf S hS (Φ.leaf (p.firstLeaf hSb))
  have h1 : S.pair (q.firstLeaf hS) = q.secondLeaf hS := sourcePair_partner S _ _ (Or.inl q.2)
  have h2 : Gsb.pair (p.firstLeaf hSb) = p.secondLeaf hSb := sourcePair_partner Gsb _ _ (Or.inl p.2)
  rw [← h1, Φ.iota_first hS hSb p, ← Φ.pair, h2]

theorem node_slotNode (hS : S.IsPlain) (hSb : Gsb.IsPlain) (s : ReplacementSlot Gsb) :
    Φ.node (slotNode hSb s) = slotNode hS (Φ.iota hS hSb s) := by
  rcases s with p | c
  · show Φ.node (p.firstLeaf hSb).toNode = ((pairOfLeaf S hS (Φ.leaf (p.firstLeaf hSb))).firstLeaf hS).toNode
    rw [Φ.iota_first, Φ.leaf_node]
  · exact (Φ.br_node c).symm

theorem iota_inj (hS : S.IsPlain) (hSb : Gsb.IsPlain) : Function.Injective (Φ.iota hS hSb) := by
  rintro (p | c) (p' | c') h
  · have h1 := congrArg (fun s : ReplacementSlot S => match s with
      | .inl q => (q.firstLeaf hS : GLeaf S.tree) | .inr _ => Φ.leaf (p.firstLeaf hSb)) h
    simp only [iota] at h1
    rw [Φ.iota_first, Φ.iota_first] at h1
    have h2 := Φ.leaf_inj h1
    have := congrArg (pairOfLeaf Gsb hSb) h2
    rw [pairOfLeaf_firstLeaf, pairOfLeaf_firstLeaf] at this
    rw [this]
  · cases h
  · cases h
  · simp only [iota, Sum.inr.injEq] at h
    rw [Φ.br_inj h]

theorem iota_mem_outer (hS : S.IsPlain) (hSb : Gsb.IsPlain) (s : ReplacementSlot Gsb) :
    Φ.iota hS hSb s ∈ outerSlots blk hS := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hj => ?_⟩
  rcases s with p | c
  · rw [iota, mem_regSlots_inl, Φ.iota_first] at hj
    have hr := (leaf_mem_clRealizationNodes _).mpr hj
    rcases Φ.ret_leaf (p.firstLeaf hSb) j with h | h
    · exact h hr
    · exact leaf_ne_branch h
  · rw [iota, mem_regSlots_inr] at hj
    exact not_ret_inter hj (Φ.ret_br c)

theorem exists_iota (hS : S.IsPlain) (hSb : Gsb.IsPlain) {s : ReplacementSlot S} (hs : s ∈ outerSlots blk hS) :
    ∃ s', Φ.iota hS hSb s' = s := by
  have hr := ret_slotNode hS hs
  rcases s with p | c
  · obtain ⟨m, hm⟩ := Φ.exists_leaf (ℓ := p.firstLeaf hS) hr
    have hsm : nodeSign Gsb.sig m.1 = 1 := by
      rw [← Φ.leaf_sign, hm]; exact sourcePair_first_sign S hS p
    refine ⟨.inl (pairOfLeaf Gsb hSb m), ?_⟩
    show Sum.inl (pairOfLeaf S hS (Φ.leaf ((pairOfLeaf Gsb hSb m).firstLeaf hSb))) = _
    rw [pairOfLeaf_first_of_positive Gsb hSb m hsm, hm, pairOfLeaf_firstLeaf]
  · obtain ⟨c', hc'⟩ := Φ.exists_br hr
    exact ⟨.inr c', congrArg Sum.inr hc'⟩

/-- Products over the outer slots of the skeleton are products over the slots of `G_sb`. -/
theorem prod_outer_iota (hS : S.IsPlain) (hSb : Gsb.IsPlain) {M : Type*} [CommMonoid M]
    (f : ReplacementSlot S → M) : ∏ s ∈ outerSlots blk hS, f s = ∏ s', f (Φ.iota hS hSb s') := by
  classical
  symm
  refine Finset.prod_bij (fun s' _ => Φ.iota hS hSb s') (fun s' _ => Φ.iota_mem_outer hS hSb s')
    (fun a _ b _ h => Φ.iota_inj hS hSb h) (fun s hs => ?_) (fun _ _ => rfl)
  obtain ⟨s', hs'⟩ := Φ.exists_iota hS hSb hs
  exact ⟨s', Finset.mem_univ _, hs'⟩

/-! ## Clock sources -/

/-- `G_sb` clock sources as skeleton clock sources. -/
def srcMap : ClkSrc Gsb → ClkSrc S := Sum.map id Φ.br

theorem clockOf_srcMap (hd : Disj blk) (tt : Fin w → ℝ) (τ' : GBranch Gsb.tree → ℝ)
    (τs : ∀ j, CLInternalTime (regionOf (blk j))) (y : ClkSrc Gsb) :
    clockOf S tt (Φ.glueTime hd τ' τs) (Φ.srcMap y) = clockOf Gsb tt τ' y := by
  rcases y with i | c
  · rfl
  · exact Φ.glueTime_br hd τ' τs c

theorem clkOfNode_root (x : GNode S.tree) (h : x.1.2 = []) : clkOfNode S x = Sum.inl x.1.1 := by
  unfold clkOfNode
  rw [nodeToSlot, dif_pos h]

theorem clk_node (y : GNode Gsb.tree) :
    clkOfNode S (Φ.node y) = Φ.srcMap (clkOfNode Gsb y) ∨ ∃ j, clkOfNode S (Φ.node y) = Sum.inr (blk j).lower := by
  by_cases hn : y.1.2 = []
  · left
    rw [clkOfNode_root _ hn, clkOfNode_root _ ((Φ.root_iff y).mpr hn), Φ.tree_eq]
    rfl
  · have hn' : (Φ.node y).1.2 ≠ [] := (Φ.root_iff y).not.mpr hn
    rw [clkOfNode_nonroot _ hn', clkOfNode_nonroot _ hn]
    obtain ⟨i, hi⟩ := child_parent y hn
    set u := y.parent hn
    rcases Φ.node_child_parent u i with ⟨hh, hp⟩ | ⟨j, hj, hc⟩
    · left
      have : (Φ.node y).parent hn' = Φ.br u := by
        have e : Φ.node (u.child i) = Φ.node y := by rw [hi]
        rw [← hp]
        congr 1
        exact e.symm
      rw [this]; rfl
    · rw [hi] at hc
      rcases hc with h | h | h
      · left
        have : (Φ.node y).parent hn' = Φ.br u := by
          have : ∀ (x : GNode S.tree) (hx : x = (blk j).upper.child (regionOf (blk j)).excluded)
            (hn : x.1.2 ≠ []), x.parent hn = (blk j).upper := fun x hx hn => by subst hx; exact parent_child _ _ _
          rw [this _ h, hj]
        rw [this]; rfl
      · right
        refine ⟨j, ?_⟩
        have : ∀ (x : GNode S.tree) (hx : x = (blk j).lower.child (regionOf (blk j)).positive)
          (hn : x.1.2 ≠ []), x.parent hn = (blk j).lower := fun x hx hn => by subst hx; exact parent_child _ _ _
        rw [this _ h]
      · right
        refine ⟨j, ?_⟩
        have : ∀ (x : GNode S.tree) (hx : x = (blk j).lower.child (regionOf (blk j)).negative)
          (hn : x.1.2 ≠ []), x.parent hn = (blk j).lower := fun x hx hn => by subst hx; exact parent_child _ _ _
        rw [this _ h]

/-- The clock sources of the image slot: those of `G_sb`, or a lower joint. -/
theorem argSrc_iota (hS : S.IsPlain) (hSb : Gsb.IsPlain) (s : ReplacementSlot Gsb) (i : Fin 2) :
    argSrc hS (Φ.iota hS hSb s) i = Φ.srcMap (argSrc hSb s i) ∨
      ∃ j, argSrc hS (Φ.iota hS hSb s) i = Sum.inr (blk j).lower := by
  rcases s with p | c
  · fin_cases i
    · simp only [iota, argSrc, Fin.zero_eta, Fin.isValue, ↓reduceIte, Φ.iota_first, Φ.leaf_node]
      exact Φ.clk_node _
    · simp only [iota, argSrc, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, Φ.iota_second, Φ.leaf_node]
      exact Φ.clk_node _
  · fin_cases i
    · simp only [iota, argSrc, Fin.zero_eta, Fin.isValue, ↓reduceIte, Φ.br_node]
      exact Φ.clk_node _
    · left; rfl

/-- S2's routing: a clock of `G_sb`, or the lower joint of a unit. -/
noncomputable def route (hS : S.IsPlain) (hSb : Gsb.IsPlain) (s : ReplacementSlot Gsb) (i : Fin 2) :
    ClkSrc Gsb ⊕ J := by
  classical
  exact if h : ∃ j, argSrc hS (Φ.iota hS hSb s) i = Sum.inr (blk j).lower then Sum.inr (Classical.choose h)
    else Sum.inl (argSrc hSb s i)

theorem route_natural (hS : S.IsPlain) (hSb : Gsb.IsPlain) (s : ReplacementSlot Gsb) (i : Fin 2) :
    Φ.route hS hSb s i = Sum.inl (argSrc hSb s i) ∨ ∃ j, Φ.route hS hSb s i = Sum.inr j := by
  classical
  unfold route
  split_ifs with h
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

theorem route_inl (hS : S.IsPlain) (hSb : Gsb.IsPlain) {s : ReplacementSlot Gsb} {i : Fin 2} {y : ClkSrc Gsb}
    (h : Φ.route hS hSb s i = Sum.inl y) : argSrc hS (Φ.iota hS hSb s) i = Φ.srcMap y := by
  classical
  unfold route at h
  split_ifs at h with hh
  cases h
  rcases Φ.argSrc_iota hS hSb s i with h1 | h1
  · exact h1
  · exact (hh h1).elim

theorem route_inr (hS : S.IsPlain) (hSb : Gsb.IsPlain) {s : ReplacementSlot Gsb} {i : Fin 2} {j : J}
    (h : Φ.route hS hSb s i = Sum.inr j) : argSrc hS (Φ.iota hS hSb s) i = Sum.inr (blk j).lower := by
  classical
  unfold route at h
  split_ifs at h with hh
  cases h
  exact Classical.choose_spec hh

end SpliceShape

end WaveTurbulence.VineB
