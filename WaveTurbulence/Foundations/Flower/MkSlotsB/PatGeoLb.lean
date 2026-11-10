/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeoCore
public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeoChain
public import WaveTurbulence.Foundations.Flower.MkSlotsB.RLbDom

/-! # B3s-HELPER3 B4 (R187): the lower bounds of a reconstruction — pinned native tops with a free clock

On a reconstruction `LG = layeredReconstruction D hS layer hLayer` with the pattern pins `fixCap LG J pat t s`:

* `nativeBr sl q`: the garden branch of a native branch; a native top sits at the attached node of its clock node
  (`nativeBr_top`), its children are native nodes of the same slot (`slotOf_nativeBr_child`);
* **`pinnedTop_freeClock_cases`**: a PINNED native top whose clock (the core of `c`) is FREE is the root of the native
  couple of a CAP pair (never a chain top), pinned at `s`, and is a capped flower parent or (`dParent`) the parent of
  one; the `dChild` tops have a pinned clock, the `dRoot` tops a constant clock (`rootPin_classification`);
* `lbS D hS fixG s c`: `some s` iff the core of `c` is free and a pinned native top is attached at a child of `c`;
* **`lbSound_lbS`**, **`lbComplete_lbS`**: B1's `LbSound`, `LbComplete` (`RLbDom.lean`) for `lbS`;
* `lbS_spec`: a lower-bounded core is free, protected (parent of a pinned branch: `NearNode`), and in layer `p`
  (an ancestor of a capped flower). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlots.IntGeo
open WaveTurbulence.Flower.MkSlots.IntRest

namespace WaveTurbulence.Flower.MkSlotsB

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)

/-- The garden branch of a native branch. -/
def nativeBr (sl : ReplacementSlot S) (q : NativeClockBranch D sl) : GBranch (D.forest hS) :=
  sourceBranchEquiv D hS (.inr ((replacementTimeIndexEquiv D).symm ⟨sl, q⟩))

theorem slotOf_nativeBr (sl : ReplacementSlot S) (q : NativeClockBranch D sl) :
    slotOf D hS (nativeBr D hS sl q).toNode = sl := by
  cases sl with
  | inl p =>
    show slotOf D hS (subforestBranchEmbedding (nativeCoupleForest D hS p) q).toNode = _
    exact slotOf_subforestBranch D hS p q
  | inr b =>
    have h : (nativeBr D hS (.inr b) q).toNode = nativeNodeAt D hS (.inr b)
        (GBranch.toNode (tree := (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree) q) := Subtype.ext rfl
    rw [h]
    exact slotOf_nativeNodeAt D hS _ _

/-- The children of a native branch are native nodes of the same slot. -/
theorem slotOf_nativeBr_child (sl : ReplacementSlot S) (q : NativeClockBranch D sl) (k : Fin 3) :
    slotOf D hS ((nativeBr D hS sl q).child k) = sl := by
  cases sl with
  | inl p =>
    show slotOf D hS ((subforestBranchEmbedding (nativeCoupleForest D hS p) q).child k) = _
    exact slotOf_subforestBranch_child D hS p q k
  | inr b =>
    have h : (nativeBr D hS (.inr b) q).child k = nativeNodeAt D hS (.inr b)
        (GBranch.child (tree := (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree) q k) :=
      (chainContextNode_child D hS b q k).symm
    rw [h]
    exact slotOf_nativeNodeAt D hS _ _

/-- **A native top sits at the attached node of its clock node.** -/
theorem nativeBr_top (sl : ReplacementSlot S) (q : NativeClockBranch D sl) (hq : NativeTop D sl q) :
    (nativeBr D hS sl q).toNode = attachedNode D hS (nativeClockNode D hS sl q) := by
  cases sl with
  | inl p =>
    obtain ⟨⟨j, r⟩, hm⟩ := q
    have hr : r = [] := hq
    subst hr
    apply Subtype.ext
    show ((((nativeCoupleForest D hS p).root j).1.1, ((nativeCoupleForest D hS p).root j).1.2 ++ [])) =
      inflatedPosition S D.tree (coupleLeafNode hS p j)
    rw [List.append_nil]
    fin_cases j <;> rfl
  | inr b =>
    obtain ⟨⟨j, r⟩, hm⟩ := q
    have hr : r = [] := hq
    subst hr
    apply Subtype.ext
    show addrExt (inflatedPosition S D.tree b.toNode) [] = inflatedPosition S D.tree b.toNode
    simp [addrExt]

/-- A pinned native top whose clock node is a child of `c` is a child of the core of `c`. -/
theorem nativeTop_isChildOf (sl : ReplacementSlot S) (q : NativeClockBranch D sl) (hq : NativeTop D sl q)
    (c : GBranch S.tree) (i : Fin 3) (hc : nativeClockNode D hS sl q = c.child i) :
    (nativeBr D hS sl q).IsChildOf (D.coreBranch hS c) := by
  have h := nativeBr_top D hS sl q hq
  rw [hc, attachedNode_child] at h
  have hv := congrArg Subtype.val h
  refine ⟨?_, i, ?_⟩
  · have h1 := congrArg Prod.fst hv; exact h1
  · have h1 := congrArg Prod.snd hv; exact h1

variable (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  (J : Finset (Fin w)) (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf) (pat : Fin w → FixPat) (t s : ℝ)

/-- The parent of a pinned branch is protected (`NearNode`, parent case). -/
theorem parent_mem_protI {LG : LayeredGarden w} {J' : Finset (Fin w)} {pat' : Fin w → FixPat} {t' s' : ℝ}
    (kSel : Fin w → Option ℕ) {B C : GBranch LG.garden.tree} (hBC : C.IsChildOf B)
    (hC : (fixCap LG J' pat' t' s' C).isSome) : B.toNode ∈ protI LG J' pat' t' s' kSel := by
  unfold protI protectedSet
  obtain ⟨h1, k, h2⟩ := hBC
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.toNode, ⟨h1.symm, Or.inr (Or.inl ⟨?_, ?_⟩)⟩,
    Or.inr ⟨C, rfl, Or.inl hC⟩⟩
  · show C.1.2 ≠ []
    rw [h2]; simp
  · show B.1.2 = C.1.2.dropLast
    rw [h2, List.dropLast_concat]

include hcap in
/-- The slot of a capped flower parent: a core branch (its chain slot) or a branch of a cap native couple. -/
theorem cfp_slot (X : GBranch (D.forest hS))
    (hX : IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J X) :
    (∃ b, X = D.coreBranch hS b ∧ slotOf D hS X.toNode = .inr b) ∨
      ∃ q, IsCapPair S hS J q ∧ slotOf D hS X.toNode = .inl q := by
  rcases capParent_core_or_native D hS layer hLayer J hcap X hX with ⟨b, he⟩ | ⟨q, c, hq, he⟩
  · exact Or.inl ⟨b, he, by rw [he]; exact slotOf_core D hS b⟩
  · exact Or.inr ⟨q, hq, by rw [he]; exact slotOf_subforestBranch D hS q c⟩

include hcap in
/-- A capped flower parent in a native chain slot is impossible at a path `r` of length `< 2`: either the core
(then `lonePath = r`, of even non-zero length) or a native couple branch. -/
theorem chain_cfp_short (b : GBranch S.tree) (X : GBranch (D.forest hS)) (r : Path)
    (hX : X.1 = addrExt (inflatedPosition S D.tree b.toNode) r) (hr : r.length < 2)
    (hsl : slotOf D hS X.toNode = .inr b) (hne : (D.tree b).lonePath ≠ []) :
    ¬ IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J X := by
  intro hc
  rcases cfp_slot D hS layer hLayer J hcap X hc with ⟨b'', he, hs''⟩ | ⟨q, -, hsq⟩
  · rw [hsl] at hs''
    obtain rfl := Sum.inr_injective hs''
    have h2 : X.1.2 = (inflatedPosition S D.tree b.toNode).2 ++ (D.tree b).lonePath := by rw [he]; rfl
    rw [hX] at h2
    simp only [addrExt] at h2
    have h3 := List.append_cancel_left h2
    have hl := chain_lonePath_length (D.tree b)
    have hz : (D.tree b).lonePath.length ≠ 0 := fun h => hne (List.length_eq_zero_iff.mp h)
    rw [← h3] at hl hz
    omega
  · rw [hsl] at hsq
    exact Sum.inr_ne_inl hsq

include hcap in
/-- **A pinned native top with a free clock** is the root of the native couple of a cap pair, pinned at `s`; it is a
capped flower parent or (`dParent`) the parent of one. (`dChild` tops have a pinned clock — their parent is the
capped flower parent; `dRoot` tops are roots; chain tops are never pinned with a free clock.) -/
theorem pinnedTop_freeClock_cases (sl : ReplacementSlot S) (q : NativeClockBranch D sl) (hq : NativeTop D sl q)
    {v : ℝ} (hv : MkSlots.fixNative D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) sl q = some v)
    (c : GBranch S.tree) (i : Fin 3) (hc : nativeClockNode D hS sl q = c.child i)
    (hfree : MkSlots.fixCore D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) c = none) :
    ∃ p : SourcePair S, sl = .inl p ∧ IsCapPair S hS J p ∧ v = s ∧
      (IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (nativeBr D hS sl q) ∨
        (pat (nativeBr D hS sl q).1.1 = FixPat.dParent ∧
          ∃ C : GBranch (D.forest hS), IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J C ∧ C.IsChildOf (nativeBr D hS sl q))) := by
  set T := nativeBr D hS sl q with hTdef
  have hTc := nativeTop_isChildOf D hS sl q hq c i hc
  have hTnr : T.1.2 ≠ [] := by
    obtain ⟨-, k, hk⟩ := hTc; rw [hk]; simp
  have hv' : fixCap (layeredReconstruction D hS layer hLayer) J pat t s T = some v := hv
  have hvs : v = s := by
    rcases fixCap_value hv' with h | ⟨-, h0, -⟩
    · exact h
    · exact absurd h0 hTnr
  -- the pin of `T` is a capped flower parent or a `dParent` pin
  have hcases : IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J T ∨
      (pat T.1.1 = FixPat.dParent ∧
        ∃ C : GBranch (D.forest hS), IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J C ∧ C.IsChildOf T) := by
    rcases fixCap_cases hv' with ⟨h, -⟩ | ⟨-, -, h0, -⟩ | ⟨-, hp, hC, -⟩ | ⟨i', -, -, ⟨C', hC', h1, h2⟩, -⟩
    · exact Or.inl h
    · exact absurd h0 hTnr
    · exact Or.inr ⟨hp, hC⟩
    · exfalso
      have he : C' = D.coreBranch hS c := by
        apply Subtype.ext
        rw [parent_addr ⟨h1, i', h2⟩, parent_addr hTc]
      have : MkSlots.fixCore D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) c = some s := by
        show fixCap (layeredReconstruction D hS layer hLayer) J pat t s (D.coreBranch hS c) = some s
        rw [← he]
        simp [fixCap, hC']
      rw [hfree] at this
      exact absurd this (by simp)
  cases sl with
  | inr b =>
    exfalso
    have hne : (D.tree b).lonePath ≠ [] := by
      intro h0
      have hq2 := q.2
      rw [show ((decodedTree (D.tree b) (nodeSign S.sig b.1)).tree q.1.1) = (D.tree b).plug (nodeSign S.sig b.1)
        TTree.leaf from rfl, (lonePath_nil_iff _ _).mp h0] at hq2
      simp [TTree.branching] at hq2
    have hT1 : T.1 = addrExt (inflatedPosition S D.tree b.toNode) [] := by
      have h := nativeBr_top D hS (.inr b) q hq
      simp only [addrExt, List.append_nil]
      exact congrArg Subtype.val h
    rcases hcases with h | ⟨-, C, hC, hCT⟩
    · exact chain_cfp_short D hS layer hLayer J hcap b T [] hT1 (by simp) (slotOf_nativeBr D hS _ q) hne h
    · obtain ⟨h1, k, h2⟩ := hCT
      have hCn : C.toNode = T.child k := Subtype.ext (Prod.ext h1 h2)
      refine chain_cfp_short D hS layer hLayer J hcap b C [k] ?_ (by simp) ?_ hne hC
      · show C.toNode.1 = addrExt (inflatedPosition S D.tree b.toNode) [k]
        rw [hCn]
        show (T.1.1, T.1.2 ++ [k]) = _
        rw [hT1]; simp [addrExt]
      · rw [hCn]; exact slotOf_nativeBr_child D hS _ q k
  | inl p =>
    refine ⟨p, rfl, ?_, hvs, hcases⟩
    have key : ∀ X : GBranch (D.forest hS), IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J X →
        slotOf D hS X.toNode = .inl p → IsCapPair S hS J p := by
      intro X hX hXs
      rcases cfp_slot D hS layer hLayer J hcap X hX with ⟨b'', -, hs''⟩ | ⟨q', hq', hsq⟩
      · rw [hXs] at hs''; exact absurd hs'' Sum.inl_ne_inr
      · rw [hXs] at hsq; rw [Sum.inl_injective hsq]; exact hq'
    rcases hcases with h | ⟨-, C, hC, hCT⟩
    · exact key T h (slotOf_nativeBr D hS (.inl p) q)
    · obtain ⟨h1, k, h2⟩ := hCT
      have hCn : C.toNode = T.child k := Subtype.ext (Prod.ext h1 h2)
      exact key C hC (by rw [hCn]; exact slotOf_nativeBr_child D hS _ q k)

/-! ## The lower bounds `lbS` -/

/-- A pinned native top is attached at a child of `c`. -/
def PinnedTopBelow (fixG : GBranch (D.forest hS) → Option ℝ) (c : GBranch S.tree) : Prop :=
  ∃ (sl : ReplacementSlot S) (q : NativeClockBranch D sl) (i : Fin 3),
    NativeTop D sl q ∧ (MkSlots.fixNative D hS fixG sl q).isSome ∧ nativeClockNode D hS sl q = c.child i

/-- **The lower bounds read on the skeleton**: `some s` at the skeleton branches with a free core and a pinned native
top attached at one of their children. -/
def lbS (fixG : GBranch (D.forest hS) → Option ℝ) (s : ℝ) (c : GBranch S.tree) : Option ℝ :=
  if MkSlots.fixCore D hS fixG c = none ∧ PinnedTopBelow D hS fixG c then some s else none

/-- **`LbSound` for `lbS`.** -/
theorem lbSound_lbS :
    LbSound D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s)
      (lbS D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) s) := by
  intro c x hx
  unfold lbS at hx
  split_ifs at hx with h
  obtain ⟨hfree, sl, q, i, hq, hpin, hcl⟩ := h
  obtain rfl := Option.some.inj hx
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hpin
  have hTc := nativeTop_isChildOf D hS sl q hq c i hcl
  have hTnr : (nativeBr D hS sl q).1.2 ≠ [] := by
    obtain ⟨-, k, hk⟩ := hTc; rw [hk]; simp
  have hvs : v = s := by
    rcases fixCap_value (show fixCap (layeredReconstruction D hS layer hLayer) J pat t s (nativeBr D hS sl q) = some v
        from hv) with h | ⟨-, h0, -⟩
    · exact h
    · exact absurd h0 hTnr
  exact ⟨sl, q, i, hq, hvs ▸ hv, hcl, hfree⟩

/-- **`LbComplete` for `lbS`.** -/
theorem lbComplete_lbS :
    LbComplete D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s)
      (lbS D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) s) := by
  intro sl q v c i hq hv hcl hfree
  have hTc := nativeTop_isChildOf D hS sl q hq c i hcl
  have hTnr : (nativeBr D hS sl q).1.2 ≠ [] := by
    obtain ⟨-, k, hk⟩ := hTc; rw [hk]; simp
  have hvs : v = s := by
    rcases fixCap_value (show fixCap (layeredReconstruction D hS layer hLayer) J pat t s (nativeBr D hS sl q) = some v
        from hv) with h | ⟨-, h0, -⟩
    · exact h
    · exact absurd h0 hTnr
  refine ⟨s, ?_, hvs.le⟩
  unfold lbS
  split_ifs with h
  · rfl
  · exact absurd ⟨hfree, sl, q, i, hq, by rw [hv]; rfl, hcl⟩ h

end WaveTurbulence.Flower.MkSlotsB
