/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.RSlotKer
public import WaveTurbulence.Foundations.Flower.MkSlots.IntCapT
public import WaveTurbulence.Foundations.Flower.MkSlots.IntGeo
public import WaveTurbulence.Foundations.Flower.Stage1WVine.WAlign1
public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeoLb

/-! # B3s-HELPER7 WP6 (R-slot, part 1): the ambient data at the nodes of a native couple

On the reconstruction `LG = layeredReconstruction D hS layer hLayer`, every ingredient of the general slot kernel at a
node `emb a` of the native couple `N` of a skeleton pair `q` (embedding by address prefixing) is read on `N`, its root
tree indices `cplRI` (α's `capT_*` objects) and a few root data:

* `cplRR c` (the root of side `c` is a garden root), `cplRD c` (its depth), `cplRC c = rcOf LG J (root c)` (the last
  letter of its address when its garden parent is a capped flower parent), `cplQW p c` (B3's weight layer `wLay` of
  the clock source of side `c`);
* the four predicates of the pattern pins (β's `fixCap_congr`): `cfp` (α), `root_bemb_iff`, `par_bemb_iff`,
  `ch_bemb_iff`;
* the stem test `onCapStem_emb_iff` and the stem node weight `genNode_cpl` (`genC`, through `genNW_genD`);
* the node weight: `chainW_cpl_noncap` (frontier weight `fwI`, root factor at `cplQW`) and `chainW_cpl_cap` (α's
  `capT_nodeW`, with the root letters `cplRC`, `capT_nodeW_rl_congr`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlots.IntCapT
open WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine

namespace WaveTurbulence.Flower.MkSlotsI

/-! ## Generic data -/

/-- The capped-flower-parent letter above a node: the last letter of its address when its parent is a capped flower
parent, `none` otherwise (and at a root). -/
def rcOf {w : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w)) (z : GNode LG.garden.tree) : Option (Fin 3) :=
  if h : z.1.2 ≠ [] then (if IsCapFlowerParent LG J (z.parent h) then some (z.1.2.getLast h) else none) else none

/-- The stem node weight read from four data: the stem test `st`, the tree `j`, the depth `k`, and whether the tree has
a selected vertex `ex`. -/
def genD {w : ℕ} (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ) (st : Prop) (j : Fin w) (k : ℕ) (ex : Prop)
    (v : ℝ) : ℂ :=
  if st then
    (MkSlotsT.radProd ((σ j).elim [] (fun i => [2 ^ i * L]) ++ (if ex ∧ kSel j ≠ some k then [Rs j] else [])) v : ℂ) *
      (if kSel j = some k then ((chiD (|v| / Rs j) : ℝ) : ℂ) else 1)
  else 1

theorem genNW_genD {w : ℕ} {LG : LayeredGarden w} {J : Finset (Fin w)} (L : ℝ) (σ kSel : Fin w → Option ℕ)
    (Rs : Fin w → ℝ) (hone : MkSlotsS.OneFlower LG J) (B : GBranch LG.garden.tree) (v : ℝ) :
    genNW LG J L σ kSel Rs B.toNode v =
      genD L σ kSel Rs (OnCapStem LG J B.toNode ∧ ¬ IsCapFlowerParent LG J B) B.1.1 B.1.2.length
        ((selCap LG J kSel B.1.1).isSome) v := by
  rw [genNW_nf L σ kSel Rs hone B v]
  unfold genD
  split_ifs <;> rfl

theorem getLast_of_eq' {l l' : List (Fin 3)} {k : Fin 3} (h : l = l' ++ [k]) (hne : l ≠ []) :
    l.getLast hne = k := by
  subst h
  exact List.getLast_concat

/-- The frontier node weight read on a native object: tree indices `ri`, root weight layers `qw`. -/
def fwI {w d n : ℕ} (p : ℕ) (g : Fin w → Mom d → ℂ) (N : LayeredGarden n) (ri : Fin n → Fin w) (qw : Fin n → ℕ)
    (a : GNode N.garden.tree) (x : Mom d) : ℂ :=
  topPsi p (g (ri a.1.1)) (N.layer a) (rowParentLayer N qw a) x

/-! ## A rooted two-root subforest -/

section GenE

variable {w d : ℕ} (LG : LayeredGarden w) (E : Comb.RootedSubforest LG.garden.tree 2)
  (hc : LG.garden.CompletelyPaired (Comb.RootedSubforest.leafSet E)) (J : Finset (Fin w))

/-- The stem test on a couple: a capped flower of the couple below the node, on the same side. -/
def stemN (N : LayeredGarden 2) (ri : Fin 2 → Fin w) (J : Finset (Fin w)) (b : GBranch N.garden.tree) : Prop :=
  (∃ l : GLeaf N.garden.tree, capT_IsFl N ri J l ∧ l.1.1 = b.1.1 ∧ b.1.2 <+: l.1.2) ∧ ¬ capT_IsFP N ri J b

/-- A node of the couple is on the capped stem iff a capped flower of the couple lies below it. -/
theorem onCapStem_emb_iff (a : GNode (rootedLayeredGarden LG E hc).garden.tree) :
    OnCapStem LG J (capT_emb LG E hc a) ↔
      ∃ l : GLeaf (rootedLayeredGarden LG E hc).garden.tree,
        capT_IsFl (rootedLayeredGarden LG E hc) (fun c => (E.root c).1.1) J l ∧ l.1.1 = a.1.1 ∧
          a.1.2 <+: l.1.2 := by
  constructor
  · rintro ⟨ℓ, hℓ, h1, r, h2⟩
    have h1' : ℓ.1.1 = (E.root a.1.1).1.1 := h1.symm
    have h2' : ((E.root a.1.1).1.2 ++ a.1.2) ++ r = ℓ.1.2 := h2
    have hv : ℓ.1 = ((E.root a.1.1).1.1, (E.root a.1.1).1.2 ++ (a.1.2 ++ r)) := by
      refine Prod.ext h1' ?_
      rw [← h2']
      exact List.append_assoc _ _ _
    have hl : a.1.2 ++ r ∈ (E.shape a.1.1).leaves := by
      rw [Comb.subtree_leaves_iff (E.subtree_eq a.1.1)]
      have h := ℓ.2
      rw [hv] at h
      exact h
    have hle : capT_lemb LG E hc ⟨(a.1.1, a.1.2 ++ r), hl⟩ = ℓ := Subtype.ext hv.symm
    refine ⟨⟨(a.1.1, a.1.2 ++ r), hl⟩, ?_, rfl, List.prefix_append _ _⟩
    refine (capT_isCapFlower_iff LG E hc J _ (fun _ => rfl) _).mp ?_
    rw [hle]
    exact hℓ
  · rintro ⟨l, hl, h1, h2⟩
    refine ⟨capT_lemb LG E hc l, (capT_isCapFlower_iff LG E hc J _ (fun _ => rfl) l).mpr hl, ?_, ?_⟩
    · show (E.root a.1.1).1.1 = (E.root l.1.1).1.1
      rw [h1]
    · show (E.root a.1.1).1.2 ++ a.1.2 <+: (E.root l.1.1).1.2 ++ l.1.2
      rw [h1]
      exact (List.prefix_append_right_inj _).mpr h2

/-- The stem test at an embedded couple branch. -/
theorem stem_bemb_iff (b : GBranch (rootedLayeredGarden LG E hc).garden.tree) :
    (OnCapStem LG J (capT_bemb LG E hc b).toNode ∧ ¬ IsCapFlowerParent LG J (capT_bemb LG E hc b)) ↔
      stemN (rootedLayeredGarden LG E hc) (fun c => (E.root c).1.1) J b := by
  rw [← capT_emb_toNode, onCapStem_emb_iff LG E hc J b.toNode,
    capT_cfp_iff LG E hc J _ (fun _ => rfl) b]
  rfl

/-- Root predicate of the pins at an embedded couple branch. -/
theorem root_bemb_iff (b : GBranch (rootedLayeredGarden LG E hc).garden.tree) :
    (capT_bemb LG E hc b).1.2 = [] ↔ b.1.2 = [] ∧ (E.root b.1.1).1.2 = [] := by
  show (E.root b.1.1).1.2 ++ b.1.2 = [] ↔ _
  rw [List.append_eq_nil_iff]
  exact And.comm

/-- `dParent` predicate of the pins at an embedded couple branch: its children are couple nodes. -/
theorem par_bemb_iff (b : GBranch (rootedLayeredGarden LG E hc).garden.tree) :
    (∃ C : GBranch LG.garden.tree, IsCapFlowerParent LG J C ∧ C.IsChildOf (capT_bemb LG E hc b)) ↔
      ∃ c : GBranch (rootedLayeredGarden LG E hc).garden.tree,
        capT_IsFP (rootedLayeredGarden LG E hc) (fun c => (E.root c).1.1) J c ∧ c.IsChildOf b := by
  constructor
  · rintro ⟨C, hC, h1, i, h2⟩
    have hv : C.1 = ((E.root b.1.1).1.1, (E.root b.1.1).1.2 ++ (b.1.2 ++ [i])) := by
      refine Prod.ext h1 ?_
      rw [h2]
      exact List.append_assoc _ _ _
    have hbr : b.1.2 ++ [i] ∈ (E.shape b.1.1).branching := by
      rw [Comb.subtree_branching_iff (E.subtree_eq b.1.1)]
      have h := C.2
      rw [hv] at h
      exact h
    have hCe : capT_bemb LG E hc ⟨(b.1.1, b.1.2 ++ [i]), hbr⟩ = C := Subtype.ext hv.symm
    refine ⟨⟨(b.1.1, b.1.2 ++ [i]), hbr⟩, ?_, rfl, i, rfl⟩
    refine (capT_cfp_iff LG E hc J _ (fun _ => rfl) _).mp ?_
    rw [hCe]
    exact hC
  · rintro ⟨c, hc', h1, i, h2⟩
    refine ⟨capT_bemb LG E hc c, (capT_cfp_iff LG E hc J _ (fun _ => rfl) c).mpr hc', ?_, i, ?_⟩
    · show (E.root c.1.1).1.1 = (E.root b.1.1).1.1
      rw [h1]
    · show (E.root c.1.1).1.2 ++ c.1.2 = ((E.root b.1.1).1.2 ++ b.1.2) ++ [i]
      rw [h1, h2, List.append_assoc]

/-- `dChild` predicate of the pins at an embedded couple branch: the parent is in the couple, or (at a couple root) it
is the garden parent of the root, read by `rcOf`. -/
theorem ch_bemb_iff (b : GBranch (rootedLayeredGarden LG E hc).garden.tree) (i : Fin 3) :
    (∃ C : GBranch LG.garden.tree, IsCapFlowerParent LG J C ∧ (capT_bemb LG E hc b).1.1 = C.1.1 ∧
        (capT_bemb LG E hc b).1.2 = C.1.2 ++ [i]) ↔
      (∃ c : GBranch (rootedLayeredGarden LG E hc).garden.tree,
          capT_IsFP (rootedLayeredGarden LG E hc) (fun c => (E.root c).1.1) J c ∧ b.1.1 = c.1.1 ∧
            b.1.2 = c.1.2 ++ [i]) ∨
        (b.1.2 = [] ∧ rcOf LG J (E.root b.1.1) = some i) := by
  constructor
  · rintro ⟨C, hC, h1, h2⟩
    change (E.root b.1.1).1.2 ++ b.1.2 = C.1.2 ++ [i] at h2
    by_cases hb : b.1.2 = []
    · right
      rw [hb, List.append_nil] at h2
      have hR : (E.root b.1.1).1.2 ≠ [] := by rw [h2]; simp
      refine ⟨hb, ?_⟩
      have hpar : (E.root b.1.1).parent hR = C := by
        apply Subtype.ext
        show ((E.root b.1.1).1.1, (E.root b.1.1).1.2.dropLast) = C.1
        rw [h2, List.dropLast_concat]
        exact Prod.ext h1 rfl
      unfold rcOf
      rw [dif_pos hR, hpar, if_pos hC]
      exact congrArg some (getLast_of_eq' h2 hR)
    · left
      have hb' : b.1.2 = b.1.2.dropLast ++ [b.1.2.getLast hb] := (List.dropLast_append_getLast hb).symm
      rw [hb', ← List.append_assoc] at h2
      obtain ⟨h3, h4⟩ := List.append_inj' h2 rfl
      have hi : b.1.2.getLast hb = i := by simpa using h4
      set c : GBranch (rootedLayeredGarden LG E hc).garden.tree := b.toNode.parent hb with hcdef
      have hCe : capT_bemb LG E hc c = C := by
        apply Subtype.ext
        show ((E.root b.1.1).1.1, (E.root b.1.1).1.2 ++ b.1.2.dropLast) = C.1
        exact Prod.ext h1 h3
      refine ⟨c, ?_, rfl, ?_⟩
      · refine (capT_cfp_iff LG E hc J _ (fun _ => rfl) c).mp ?_
        rw [hCe]
        exact hC
      · show b.1.2 = b.1.2.dropLast ++ [i]
        rw [← hi]
        exact hb'
  · rintro (⟨c, hc', h1, h2⟩ | ⟨hb, hrc⟩)
    · refine ⟨capT_bemb LG E hc c, (capT_cfp_iff LG E hc J _ (fun _ => rfl) c).mpr hc', ?_, ?_⟩
      · show (E.root b.1.1).1.1 = (E.root c.1.1).1.1
        rw [h1]
      · show (E.root b.1.1).1.2 ++ b.1.2 = ((E.root c.1.1).1.2 ++ c.1.2) ++ [i]
        rw [h1, h2, List.append_assoc]
    · unfold rcOf at hrc
      by_cases hR : (E.root b.1.1).1.2 ≠ []
      · rw [dif_pos hR] at hrc
        by_cases hC : IsCapFlowerParent LG J ((E.root b.1.1).parent hR)
        · rw [if_pos hC] at hrc
          have hi := Option.some.inj hrc
          refine ⟨(E.root b.1.1).parent hR, hC, rfl, ?_⟩
          show (E.root b.1.1).1.2 ++ b.1.2 = (E.root b.1.1).1.2.dropLast ++ [i]
          rw [hb, List.append_nil, ← hi]
          exact (List.dropLast_append_getLast hR).symm
        · rw [if_neg hC] at hrc
          exact absurd hrc (by simp)
      · rw [dif_neg hR] at hrc
        exact absurd hrc (by simp)

/-- The couple kernel's node weight `capT_nodeW` reads the root letters only at capped flower roots. -/
theorem capT_nodeW_rl_congr (L γ δ : ℝ) (p : ℕ) (s : ℝ) (Rf : Fin w → Option ℝ)
    (dag : Option (Fin w → Fin 3 → Mom d)) (N : LayeredGarden 2) (ri : Fin 2 → Fin w)
    (rl rl' : Fin 2 → Option (Fin 3))
    (h : ∀ a : GNode N.garden.tree, a.1.2 = [] →
      (∃ l : GLeaf N.garden.tree, capT_IsFl N ri J l ∧ l.toNode = a) → rl a.1.1 = rl' a.1.1)
    (a : GNode N.garden.tree) (x : Mom d) :
    capT_nodeW L γ δ p s J Rf dag N ri rl a x = capT_nodeW L γ δ p s J Rf dag N ri rl' a x := by
  unfold capT_nodeW capT_dag
  congr 1
  cases dag with
  | none => rfl
  | some cc =>
    simp only [Option.elim]
    congr 1
    unfold capT_ch
    by_cases ha : a.1.2 = []
    · rw [dif_pos ha, dif_pos ha]
      by_cases hf : ∃ l : GLeaf N.garden.tree, capT_IsFl N ri J l ∧ l.toNode = a
      · rw [h a ha hf]
      · have h1 : ∀ o : Option (Fin 3), o.elim 1 (fun i =>
            if ∃ l : GLeaf N.garden.tree, capT_IsFl N ri J l ∧ l.toNode = a then
              Complex.exp (((-(capT_theta L γ δ s (if i = 1 then -N.garden.sign a else N.garden.sign a) *
                childSign i * ‖x‖ ^ 2) : ℝ) : ℂ) * Complex.I) else 1) = 1 := by
          intro o
          cases o with
          | none => rfl
          | some i => exact if_neg hf
        rw [h1, h1]
    · rw [dif_neg ha, dif_neg ha]

/-- At a capped flower root of the couple, the root letter is `rcOf` of the root. -/
theorem rl_eq_rcOf (a : GNode (rootedLayeredGarden LG E hc).garden.tree) (ha : a.1.2 = [])
    (hf : ∃ l : GLeaf (rootedLayeredGarden LG E hc).garden.tree,
      capT_IsFl (rootedLayeredGarden LG E hc) (fun c => (E.root c).1.1) J l ∧ l.toNode = a) :
    (E.root a.1.1).1.2.getLast? = rcOf LG J (E.root a.1.1) := by
  unfold rcOf
  by_cases hR : (E.root a.1.1).1.2 ≠ []
  · rw [dif_pos hR, List.getLast?_eq_getLast hR]
    obtain ⟨l, hl, hla⟩ := hf
    have hea : capT_emb LG E hc a = E.root a.1.1 := by
      apply Subtype.ext
      show ((E.root a.1.1).1.1, (E.root a.1.1).1.2 ++ a.1.2) = (E.root a.1.1).1
      rw [ha, List.append_nil]
    have hlv : (capT_lemb LG E hc l).1 = (E.root a.1.1).1 := by
      have h1 := congrArg Subtype.val ((subforest_leaf_node E l).trans (congrArg _ hla))
      exact h1.trans (congrArg Subtype.val hea)
    have hC : IsCapFlowerParent LG J ((E.root a.1.1).parent hR) := by
      refine ⟨capT_lemb LG E hc l, (capT_isCapFlower_iff LG E hc J _ (fun _ => rfl) l).mpr hl, ?_,
        (E.root a.1.1).1.2.getLast hR, ?_⟩
      · rw [hlv]; rfl
      · rw [hlv]
        exact (List.dropLast_append_getLast hR).symm
    rw [if_pos hC]
  · rw [dif_neg hR]
    rw [not_not] at hR
    rw [hR]
    rfl

end GenE

/-! ## The native couple of a skeleton pair -/

section Couple

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (J : Finset (Fin w))
  (q : SourcePair S)

/-- The tree index of side `c`. -/
def cplRI (c : Fin 2) : Fin w := ((nativeCoupleForest D hS q).root c).1.1

/-- The root of side `c` is a garden root. -/
def cplRR (c : Fin 2) : Prop := ((nativeCoupleForest D hS q).root c).1.2 = []

/-- The depth of the root of side `c`. -/
def cplRD (c : Fin 2) : ℕ := ((nativeCoupleForest D hS q).root c).1.2.length

/-- The capped-flower-parent letter above the root of side `c`. -/
def cplRC (c : Fin 2) : Option (Fin 3) :=
  rcOf (layeredReconstruction D hS layer hLayer) J ((nativeCoupleForest D hS q).root c)

/-- The weight layer of the clock source of side `c` (B3's `wLay`). -/
def cplQW (p : ℕ) (c : Fin 2) : ℕ :=
  Stage1WVine.wLay p (fun b => layer (D.coreBranch hS b).toNode) (Represents.argSrc hS (.inl q) c)

/-- The stem node weight on a native couple. -/
def genC (N : LayeredGarden 2) (ri : Fin 2 → Fin w) (rd : Fin 2 → ℕ) (ex : Fin w → Prop) (J : Finset (Fin w))
    (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ) (a : GNode N.garden.tree) (v : ℝ) : ℂ :=
  if hb : a.1.2 ∈ (N.garden.tree a.1.1).branching then
    genD L σ kSel Rs (stemN N ri J ⟨a.1, hb⟩) (ri a.1.1) (rd a.1.1 + a.1.2.length) (ex (ri a.1.1)) v
  else 1

/-- A native couple node is never a core node. -/
theorem cpl_not_core (a : GNode (nativeCoupleLayered D hS layer hLayer q).garden.tree) (β : GBranch S.tree) :
    (nativeCoupleForest D hS q).nodeEmbedding a ≠ (D.coreBranch hS β).toNode := by
  intro h
  have h2 : nativeNodeMap D hS ⟨.inl q, a⟩ =
      nativeNodeMap D hS ⟨.inr β, (chainLoneLeaf (D.tree β) (nodeSign S.sig β.1)).toNode⟩ :=
    h.trans (chainContextNode_lone D hS β).symm
  have h3 := congrArg Sigma.fst (nativeNodeMap_injective D hS h2)
  exact Sum.inl_ne_inr h3

/-- **The per-node factor of `genΘs` at a native couple node.** -/
theorem genNode_cpl (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (hone : MkSlotsS.OneFlower (layeredReconstruction D hS layer hLayer) J)
    (a : GNode (nativeCoupleLayered D hS layer hLayer q).garden.tree) (v : ℝ) :
    genNode D hS layer hLayer J L σ kSel Rs ((nativeCoupleForest D hS q).nodeEmbedding a) v =
      genC (nativeCoupleLayered D hS layer hLayer q) (cplRI D hS q) (cplRD D hS q)
        (fun j => (selCap (layeredReconstruction D hS layer hLayer) J kSel j).isSome) J L σ kSel Rs a v := by
  set E := nativeCoupleForest D hS q
  have hc := nativeCoupleForest_closed D hS q
  unfold genNode
  rw [if_neg (fun ⟨β, hβ⟩ => cpl_not_core D hS layer hLayer q a β hβ)]
  unfold genC
  by_cases hb : a.1.2 ∈ ((nativeCoupleLayered D hS layer hLayer q).garden.tree a.1.1).branching
  · rw [dif_pos hb]
    have he : E.nodeEmbedding a =
        (capT_bemb (layeredReconstruction D hS layer hLayer) E hc ⟨a.1, hb⟩).toNode := Subtype.ext rfl
    rw [he, genNW_genD L σ kSel Rs hone]
    have hst := stem_bemb_iff (layeredReconstruction D hS layer hLayer) E hc J ⟨a.1, hb⟩
    have hl : (capT_bemb (layeredReconstruction D hS layer hLayer) E hc ⟨a.1, hb⟩).1.2.length =
        cplRD D hS q a.1.1 + a.1.2.length := by
      show ((E.root a.1.1).1.2 ++ a.1.2).length = _
      rw [List.length_append]
      rfl
    rw [hl, propext hst]
    rfl
  · rw [dif_neg hb]
    apply genNW_not_branch
    intro h
    exact hb ((Comb.subtree_branching_iff (E.subtree_eq a.1.1) a.1.2).mpr h)

/-- **The node weight at a native couple node of a non-cap pair**: the frontier weight `fwI`. -/
theorem chainW_cpl_noncap (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf) (L γ δ : ℝ) (p : ℕ) (s : ℝ)
    (Rf : Fin w → Option ℝ) (dag : Option (Fin w → Fin 3 → Mom d)) (hq : ¬ IsCapPair S hS J q)
    (a : GNode (nativeCoupleLayered D hS layer hLayer q).garden.tree) (x : Mom d) :
    chainW D hS layer hLayer L γ δ p s J Rf dag ((nativeCoupleForest D hS q).nodeEmbedding a) x =
      fwI p (fun j => frontierG (Rf j)) (nativeCoupleLayered D hS layer hLayer q) (cplRI D hS q)
        (cplQW D hS layer q p) a x := by
  have hnc : ¬ InCapNative D hS J ((nativeCoupleForest D hS q).nodeEmbedding a) :=
    IntGeo.not_inCapNative_of_slot D hS J (.inl q) (fun q' h => by cases h; exact hq) a
  rw [IntGeo.chainW_eq_fwNode D hS layer hLayer J hcap L γ δ p s Rf dag _ x hnc]
  rw [fwNode_embed (layeredReconstruction D hS layer hLayer) (nativeCoupleLayered D hS layer hLayer q)
    (fun a => (nativeCoupleForest D hS q).nodeEmbedding a) (fun j => ((nativeCoupleForest D hS q).root j).1)
    (fun a => rfl) (fun a => rfl) p (fun j => frontierG (Rf j)) a x]
  unfold fwI
  by_cases ha : a.1.2 = []
  · have har : a = GNode.root (nativeCoupleLayered D hS layer hLayer q).garden.tree a.1.1 :=
      Subtype.ext (Prod.ext rfl ha)
    unfold rowParentLayer
    rw [if_pos ha, if_pos ha]
    have e := Stage1WVine.cplQ_root_factor D hS layer hLayer p (frontierG (Rf (cplRI D hS q a.1.1))) q a.1.1 x
    rw [← har] at e
    exact e
  · unfold rowParentLayer
    rw [if_neg ha, if_neg ha]
    rfl

/-- **The node weight at a native couple node of a cap pair**: α's couple weight `capT_nodeW` with the root letters
`cplRC`. -/
theorem chainW_cpl_cap {p : ℕ} (hG : CapGeo (layeredReconstruction D hS layer hLayer) J p) (L γ δ : ℝ) (s : ℝ)
    (Rf : Fin w → Option ℝ) (dag : Option (Fin w → Fin 3 → Mom d)) (hq : IsCapPair S hS J q)
    (a : GNode (nativeCoupleLayered D hS layer hLayer q).garden.tree) (x : Mom d) :
    chainW D hS layer hLayer L γ δ p s J Rf dag ((nativeCoupleForest D hS q).nodeEmbedding a) x =
      capT_nodeW L γ δ p s J Rf dag (nativeCoupleLayered D hS layer hLayer q) (cplRI D hS q)
        (cplRC D hS layer hLayer J q) a x := by
  have hc := nativeCoupleForest_closed D hS q
  have hin : InCapNative D hS J ((nativeCoupleForest D hS q).nodeEmbedding a) :=
    IntGeo.inCapNative_nativeNodeAt D hS J q hq a
  have e0 : chainW D hS layer hLayer L γ δ p s J Rf dag ((nativeCoupleForest D hS q).nodeEmbedding a) x =
      capNodeW L γ δ p s (layeredReconstruction D hS layer hLayer) J Rf dag
        ((nativeCoupleForest D hS q).nodeEmbedding a) x := by
    unfold chainW capNodeW
    rw [ite_eq_left hin]
  have hcp : ∃ c₀, (fun c => ((nativeCoupleForest D hS q).root c).1.1) c₀ ∈ J := by
    obtain ⟨c, hc'⟩ := capT_exists_cap D hS J q hq
    refine ⟨c, ?_⟩
    show ((nativeCoupleForest D hS q).root c).1.1 ∈ J
    rw [capT_root_val]
    exact hc'
  refine e0.trans ((capT_nodeW_eq (layeredReconstruction D hS layer hLayer) (nativeCoupleForest D hS q) hc J
    (fun c => ((nativeCoupleForest D hS q).root c).1.1) (fun _ => rfl) hG hcp L γ δ s Rf dag
    (fun c => ((nativeCoupleForest D hS q).root c).1.2.getLast?) (fun _ => rfl) a x).trans ?_)
  refine capT_nodeW_rl_congr J L γ δ p s Rf dag _ _ _ _ (fun a' ha' hf => ?_) a x
  exact rl_eq_rcOf (layeredReconstruction D hS layer hLayer) (nativeCoupleForest D hS q) hc J a' ha' hf

/-- The anchored profile at a native couple node (α's `capT_prof_eq`). -/
theorem anch_cpl {d' : ℕ} (h : ℕ → Fin w → Fin w → Mom d' → ℝ) (L : ℝ) (roots : Fin w → (Fin d' → ℤ))
    (a : GNode (nativeCoupleLayered D hS layer hLayer q).garden.tree) :
    anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots ((nativeCoupleForest D hS q).nodeEmbedding a).1 =
      capT_prof J (nativeCoupleLayered D hS layer hLayer q) (cplRI D hS q) h L roots a :=
  capT_prof_eq (layeredReconstruction D hS layer hLayer) (nativeCoupleForest D hS q)
    (nativeCoupleForest_closed D hS q) J _ (fun _ => rfl) h L roots a

end Couple

end WaveTurbulence.Flower.MkSlotsI
