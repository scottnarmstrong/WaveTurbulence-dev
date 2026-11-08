/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.SlotObl
public import WaveTurbulence.Foundations.Flower.MkSlotsS.EngMom

/-! # B3s-HELPER7 (WP9): counting the slot losses

Two counting facts pay the slot losses of `GenSlotObligation` over the outer slots:

* **protected natives** (`card_protNative_le`, `card_protNative_iota_le`): at most `|Π|` slots carry a node of the
  protected set `Π` as a native node (`HasProtNative`), since a node of the reconstruction determines its slot
  (`MkSlots.slotOf_nativeNodeAt`); through the injective slot embedding `Φ.iota` of a splice shape the same bound
  holds over the slots of the spliced skeleton. Product form `prod_protLoss_le`:
  `∏_{s'} L^{[HasProtNative (ι s')] · genLossExp d} ≤ L^{genLossExp d · |Π|}`.
* **selection-adjacent slots** (`card_adjS_le`): a slot reading a selected branch `v` as a clock is `.inr v` itself
  (second clock) or the slot of one of the three children of `v` (first clock of a chain slot; a leaf clock of a
  couple slot), so at most `4 |sel|` slots are `AdjS`. Product form `prod_adjS_le`:
  `∏_s (AdjS s ? c : 1) ≤ c^{4 |sel|}` for `1 ≤ c` (e.g. `∏_s selF s ≤ 3^{4 |sel|}`, `prod_selF_le`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.RedSplice

namespace WaveTurbulence.Flower.MkSlotsI

variable {w d : ℕ}

/-! ## Slots carrying protected native nodes -/

section Prot

variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer)

/-- **At most `|Π|` slots carry a protected native node**: a node of `Π` determines the slot it is native to. -/
theorem card_protNative_le (Pi : Finset (GNode (layeredReconstruction D hS layer hLayer).garden.tree)) :
    (Finset.univ.filter (HasProtNative D hS layer hLayer Pi)).card ≤ Pi.card := by
  refine Finset.card_le_card_of_forall_subsingleton
    (fun sl z => ∃ a : NativeNode D sl, z.1 = (nativeNodeAt D hS sl a).1) ?_ ?_
  · intro sl hsl
    obtain ⟨a, -, z, hz, hza⟩ := (Finset.mem_filter.mp hsl).2
    exact ⟨z, hz, a, hza⟩
  · rintro z - s1 ⟨-, a1, h1⟩ s2 ⟨-, a2, h2⟩
    have h : nativeNodeAt D hS s1 a1 = nativeNodeAt D hS s2 a2 := Subtype.ext (h1.symm.trans h2)
    rw [← MkSlots.slotOf_nativeNodeAt D hS s1 a1, ← MkSlots.slotOf_nativeNodeAt D hS s2 a2, h]

variable {K : Type} [Fintype K] [DecidableEq K] {blk : K → CLBlock S} {Gsb : Garden w}

/-- **The same bound over the slots of a spliced skeleton**, through the injective slot embedding `Φ.iota`. -/
theorem card_protNative_iota_le (Φ : VineB.SpliceShape blk Gsb) (hSb : Gsb.IsPlain)
    (Pi : Finset (GNode (layeredReconstruction D hS layer hLayer).garden.tree)) :
    (Finset.univ.filter (fun s' : ReplacementSlot Gsb =>
      HasProtNative D hS layer hLayer Pi (Φ.iota hS hSb s'))).card ≤ Pi.card := by
  refine le_trans ?_ (card_protNative_le D hS layer hLayer Pi)
  refine Finset.card_le_card_of_injOn (Φ.iota hS hSb) ?_ ?_
  · intro s' hs'
    rw [Finset.mem_coe, Finset.mem_filter] at hs' ⊢
    exact ⟨Finset.mem_univ _, hs'.2⟩
  · exact fun a _ b _ h => Φ.iota_inj hS hSb h

theorem genLossExp_nonneg (d : ℕ) : 0 ≤ genLossExp d := by
  unfold genLossExp; positivity

/-- **Product form of the protected loss**: `∏_{s'} L^{[HasProtNative (ι s')] · genLossExp d} ≤ L^{genLossExp d · |Π|}`
for `1 ≤ L`. -/
theorem prod_protLoss_le (Φ : VineB.SpliceShape blk Gsb) (hSb : Gsb.IsPlain)
    (Pi : Finset (GNode (layeredReconstruction D hS layer hLayer).garden.tree)) {L : ℝ} (hL : 1 ≤ L) :
    ∏ s' : ReplacementSlot Gsb,
      L ^ (if HasProtNative D hS layer hLayer Pi (Φ.iota hS hSb s') then genLossExp d else 0) ≤
      L ^ (genLossExp d * (Pi.card : ℝ)) := by
  rw [← Real.rpow_sum_of_pos (by linarith)]
  refine Real.rpow_le_rpow_of_exponent_le hL ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (genLossExp_nonneg d)
  exact_mod_cast card_protNative_iota_le D hS layer hLayer Φ hSb Pi

end Prot

/-! ## Slots adjacent to selected branches -/

section Adj

variable {G : Garden w} (hS : G.IsPlain)

/-- The slot reading the clock of a node as a first (chain) or leaf (couple) clock: the chain slot of a branching node,
the couple slot of a leaf. -/
def nodeSlotOf (x : GNode G.tree) : ReplacementSlot G :=
  if h : x.1.2 ∈ (G.tree x.1.1).branching then Sum.inr ⟨x.1, h⟩
  else Sum.inl (pairOfLeaf G hS ⟨x.1, ((TTree.mem_nodes_iff _ _).mp x.2).resolve_right h⟩)

theorem nodeSlotOf_branch (b : GBranch G.tree) : nodeSlotOf hS b.toNode = Sum.inr b := by
  unfold nodeSlotOf
  split
  · rfl
  · next h => exact absurd b.2 h

theorem nodeSlotOf_leaf (ℓ : GLeaf G.tree) : nodeSlotOf hS ℓ.toNode = Sum.inl (pairOfLeaf G hS ℓ) := by
  unfold nodeSlotOf
  split
  · next h => exact (TTree.not_mem_branching_of_mem_leaves _ ℓ.2 h).elim
  · rfl

/-- A node whose parent clock is the branch `v` is a child of `v`. -/
theorem exists_child_of_clkOfNode {v : GBranch G.tree} {x : GNode G.tree} (h : clkOfNode G x = Sum.inr v) :
    ∃ k : Fin 3, v.child k = x := by
  by_cases hn : x.1.2 = []
  · unfold clkOfNode at h
    rw [nodeToSlot, dite_eq_left hn] at h
    exact absurd h (by simp)
  · rw [VineB.clkOfNode_nonroot x hn, Sum.inr.injEq] at h
    exact ⟨x.1.2.getLast hn, by rw [← h]; exact Reg.Skeleton.child_parent x hn⟩

/-- The (at most) four slots reading the branch `v` as a clock: `.inr v`, and the slots of its three children. -/
def adjSlots (v : GBranch G.tree) : Fin 4 → ReplacementSlot G :=
  Fin.cons (Sum.inr v) (fun k : Fin 3 => nodeSlotOf hS (v.child k))

/-- **A slot reading `v` as a clock is one of the four `adjSlots v`.** -/
theorem exists_adjSlots_of_argSrc {s : ReplacementSlot G} {i : Fin 2} {v : GBranch G.tree}
    (h : argSrc hS s i = Sum.inr v) : ∃ k : Fin 4, adjSlots hS v k = s := by
  have hchild : ∀ x : GNode G.tree, clkOfNode G x = Sum.inr v → nodeSlotOf hS x = s →
      ∃ k : Fin 4, adjSlots hS v k = s := by
    intro x hx hs
    obtain ⟨k, rfl⟩ := exists_child_of_clkOfNode hx
    exact ⟨k.succ, by simp only [adjSlots, Fin.cons_succ]; exact hs⟩
  rcases s with p | b
  · by_cases hi : i = 0
    · simp only [argSrc, hi, ↓reduceIte] at h
      exact hchild _ h (by rw [nodeSlotOf_leaf, pairOfLeaf_firstLeaf])
    · simp only [argSrc, hi, ↓reduceIte] at h
      exact hchild _ h (by rw [nodeSlotOf_leaf, pairOfLeaf_secondLeaf])
  · by_cases hi : i = 0
    · simp only [argSrc, hi, ↓reduceIte] at h
      exact hchild _ h (nodeSlotOf_branch hS b)
    · simp only [argSrc, hi, ↓reduceIte, Sum.inr.injEq] at h
      exact ⟨0, by simp only [adjSlots, Fin.cons_zero, h]⟩

variable {J : Type} (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J) (sel : Finset (GBranch G.tree))

/-- **At most `4 |sel|` slots are adjacent to a selected branch.** -/
theorem card_adjS_le (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j) :
    (Finset.univ.filter (MkSlotsS.AdjS route sel)).card ≤ 4 * sel.card := by
  have hsub : Finset.univ.filter (MkSlotsS.AdjS route sel) ⊆
      sel.biUnion (fun v => Finset.univ.image (adjSlots hS v)) := by
    intro s hs
    obtain ⟨i, v, hv, hrv⟩ := (Finset.mem_filter.mp hs).2
    have harg : argSrc hS s i = Sum.inr v := by
      rcases hroute s i with h | ⟨j, h⟩
      · rw [h, Sum.inl.injEq] at hrv; exact hrv
      · rw [h] at hrv; exact absurd hrv (by simp)
    obtain ⟨k, hk⟩ := exists_adjSlots_of_argSrc hS harg
    exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩⟩
  calc (Finset.univ.filter (MkSlotsS.AdjS route sel)).card
      ≤ (sel.biUnion (fun v => Finset.univ.image (adjSlots hS v))).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ sel, (Finset.univ.image (adjSlots hS v)).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ sel, 4 := Finset.sum_le_sum fun v _ => by
        simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin 4))) (f := adjSlots hS v))
    _ = 4 * sel.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Product form**: `∏_s (AdjS s ? c : 1) ≤ c^{4 |sel|}` for `1 ≤ c`. -/
theorem prod_adjS_le (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j)
    {c : ℝ} (hc : 1 ≤ c) :
    ∏ s, (if MkSlotsS.AdjS route sel s then c else 1) ≤ c ^ (4 * sel.card) := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  exact pow_le_pow_right₀ hc (card_adjS_le hS route sel hroute)

/-- The selection constants of the slots: `∏_s selF s ≤ 3^{4 |sel|}`. -/
theorem prod_selF_le (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j) :
    ∏ s, MkSlotsS.selF route sel s ≤ (3 : ℝ) ^ (4 * sel.card) := by
  have h := prod_adjS_le hS route sel hroute (c := 3) (by norm_num)
  convert h using 2 with s
  unfold MkSlotsS.selF
  congr 1

end Adj

end WaveTurbulence.Flower.MkSlotsI
