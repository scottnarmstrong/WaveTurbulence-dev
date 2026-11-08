/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.CapFilt
public import WaveTurbulence.Foundations.Flower.MkSlots.IntRest
public import WaveTurbulence.Foundations.Flower.MkMark.CoordIso

/-! # B3s-HELPER8 / CAP: the geometry of a nontrivial cap slot

For a nontrivial cap slot `K` (B3s's `MkSlots.CapSide`) of a reconstruction with capped geometry:

* `native_not_core`: no native node of a cap pair is a core node (`MkSlots.IntRest.slotOf_core`);
* `hasProtNative_cap`: the capped flower is a non-core native node of the slot in the protected set (its parent, the
  capped flower parent, is pinned at `s`) — `MkSlotsI.HasProtNative`;
* the selected vertices: `selNative_eq` (the slot's selected native vertices are the images of `capSelT`),
  `capSelT_subsingleton`, `capSel_plain` (a selection forces `pat = plain`, so the configuration is `term`),
  `capSel_chain` (a selected chain vertex is a strict chain node other than the terminal one, D2b `sel_on_chain`);
* `selAdj_cap`: `SelAdj` on the cap pair forces `pat = plain` on the chain's tree and no native selection;
* `capT1_lone_layer`: the lone leaf (the capped flower) is in layer `p`;
* the box: `genBox_j0` (the chain clock of a point of `genBoxAt` is in `[p, p + 1]`), `genBox_root` (if the
  configuration pins the root and the chain clock is pinned or a root clock, the chain clock is at least the root
  pin). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open MeasureTheory Set
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.Links WaveTurbulence.LGSpine WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo
  WaveTurbulence.Flower.ProtWhole WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlotsB WaveTurbulence.Represents

namespace WaveTurbulence.Flower.MkSlotsO

/-! ### Clocks of skeleton nodes -/

theorem clkOfNode_root' {w : ℕ} {S : Garden w} (x : GNode S.tree) (h : x.1.2 = []) :
    clkOfNode S x = Sum.inl x.1.1 := by
  unfold clkOfNode
  simp only [nodeToSlot, h, ↓reduceDIte]

theorem clkOfNode_inr_fst {w : ℕ} {S : Garden w} {x : GNode S.tree} {β : GBranch S.tree}
    (h : clkOfNode S x = Sum.inr β) : β.1.1 = x.1.1 := by
  by_cases hn : x.1.2 = []
  · rw [clkOfNode_root' x hn] at h
    cases h
  · rw [VineB.clkOfNode_nonroot x hn] at h
    cases h
    rfl

/-- The pins of `fixCap` are `s` or `t`. -/
theorem fixCap_val {w : ℕ} {LG : LayeredGarden w} {J : Finset (Fin w)} {pat : Fin w → FixPat} {t s v : ℝ}
    {b : GBranch LG.garden.tree} (h : fixCap LG J pat t s b = some v) : v = s ∨ v = t := by
  unfold fixCap at h
  by_cases h1 : IsCapFlowerParent LG J b
  · simp only [h1, ↓reduceIte, Option.some.injEq] at h
    exact Or.inl h.symm
  · simp only [h1, ↓reduceIte] at h
    rcases hp : pat b.1.1 with _ | _ | _ | i <;> simp only [hp] at h
    · cases h
    · split_ifs at h
      exact Or.inr (Option.some.inj h).symm
    · split_ifs at h
      exact Or.inl (Option.some.inj h).symm
    · split_ifs at h
      exact Or.inl (Option.some.inj h).symm

namespace CapK

variable {w : ℕ} {S : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {J : Finset (Fin w)}
  {q : SourcePair S} (K : CapSide D hS J q)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {p : ℕ} (hGeo : CapGeo (layeredReconstruction D hS layer hLayer) J p)

omit K in
/-- **No native node of a cap pair is a core node.** -/
theorem native_not_core (a : NativeNode D (.inl q)) (β : GBranch S.tree) :
    nativeNodeAt D hS (.inl q) a ≠ (D.coreBranch hS β).toNode := by
  intro h
  have h1 := slotOf_nativeNodeAt D hS (.inl q) a
  rw [h, IntRest.slotOf_core D hS β] at h1
  cases h1

theorem not_capCore (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree) : ¬ capCore K layer hLayer b1 := by
  rintro ⟨β, hβ⟩
  exact native_not_core (q := q) ((K.Dq layer hLayer).ι b1.toNode) β hβ

/-! ### The protected native node -/

theorem e1_lone : K.e1 layer hLayer (K.Dq layer hLayer).lone1 = K.flower.toNode :=
  Subtype.ext (K.e1_val layer hLayer _)

include K in
/-- **The capped flower is a non-core native node of the cap slot in the protected set.** -/
theorem hasProtNative_cap (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ) :
    MkSlotsI.HasProtNative D hS layer hLayer (protI (layeredReconstruction D hS layer hLayer) J pat t s kSel)
      (.inl q) := by
  refine ⟨(K.Dq layer hLayer).ι (K.Dq layer hLayer).lone1, fun β => native_not_core (q := q) _ β, K.flower.toNode,
    ?_, by rw [← e1_lone K layer hLayer]; rfl⟩
  unfold protI protectedSet
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, K.bF.toNode, ?_, Or.inr ⟨K.bF, rfl, Or.inl ?_⟩⟩
  · have hf : K.flower.1 = (K.bF.1.1, K.bF.1.2 ++ [K.iF]) := K.flower_val
    have h2 : K.flower.1.2 = K.bF.1.2 ++ [K.iF] := congrArg Prod.snd hf
    refine ⟨?_, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
    · show K.flower.1.1 = K.bF.1.1
      have h1 := congrArg Prod.fst hf
      exact h1
    · intro h
      have h' : K.flower.1.2 = [] := h
      rw [h2] at h'
      simp at h'
    · show K.flower.1.2.dropLast = K.bF.1.2
      rw [h2]; simp
  · unfold fixCap
    simp [K.isCFP_bF layer hLayer]

/-! ### Selected vertices -/

theorem capE_injective : Function.Injective (capE K layer hLayer) := by
  intro b1 b1' h
  have h2 := congrArg (fun z : GBranch (layeredReconstruction D hS layer hLayer).garden.tree => z.1.2) h
  simp only [capE, embBr, addrExt] at h2
  exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) (List.append_cancel_left h2))

theorem capE_selSet (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree) (kSel : Fin w → Option ℕ) :
    b1 ∈ capSelT K layer hLayer kSel ↔
      capE K layer hLayer b1 ∈ selSetCap (layeredReconstruction D hS layer hLayer) J kSel := by
  rw [mem_capSelT]
  refine ⟨fun h => h.2, fun h => ⟨⟨not_capCore K layer hLayer b1, ?_⟩, h⟩⟩
  exact ⟨_, (selCap_spec (selSetCap_spec h).2.1).2⟩

/-- At most one selected branch on the paired tree. -/
theorem capSelT_eq (kSel : Fin w → Option ℕ) {b1 b1' : GBranch (K.Dq layer hLayer).T1.garden.tree}
    (h : b1 ∈ capSelT K layer hLayer kSel) (h' : b1' ∈ capSelT K layer hLayer kSel) : b1 = b1' :=
  capE_injective K layer hLayer (selSetCap_eq_of_tree ((capE_selSet K layer hLayer b1 kSel).1 h)
    ((capE_selSet K layer hLayer b1' kSel).1 h') rfl)

include hGeo in
/-- A selected native vertex of the cap slot is the image of a selected branch of the paired tree. -/
theorem selNative_sub (kSel : Fin w → Option ℕ) (v : GBranch (layeredReconstruction D hS layer hLayer).garden.tree)
    (hv : v ∈ MkSlotsS.selNative D hS layer hLayer J kSel (.inl q)) :
    ∃ b1 ∈ capSelT K layer hLayer kSel, capE K layer hLayer b1 = v := by
  obtain ⟨hsel, a, -, hva⟩ := Finset.mem_filter.1 hv
  obtain ⟨o, rfl⟩ := (K.Dq layer hLayer).nodeEquiv.surjective a
  cases o with
  | none =>
    exfalso
    have hb := v.2
    have hva' : v.1 = ((nativeCoupleForest D hS q).nodeEmbedding
        (GNode.root (nativeCoupleLayered D hS layer hLayer q).garden.tree K.c)).1 := hva
    have h1 : v.1.1 = K.cleaf.1.1 := by
      rw [hva', K.cRoot_val layer hLayer]; exact inflatedPosition_index S D.tree _
    rw [h1, hGeo.cap_leaf _ K.cJ] at hb
    simp [TTree.branching] at hb
  | some a1 =>
    have hva' : v.1 = (K.e1 layer hLayer a1).1 := hva
    have hb : a1.1.2 ∈ (K.X.plug K.ζ .leaf).branching := by
      have := v.2
      rw [hva'] at this
      exact (branching_e1_iff K layer hLayer a1).1 this
    refine ⟨⟨a1.1, hb⟩, (capE_selSet K layer hLayer _ kSel).2 ?_, ?_⟩
    · have e : capE K layer hLayer ⟨a1.1, hb⟩ = v :=
        Subtype.ext (hva'.trans (K.e1_val layer hLayer a1)).symm
      rw [e]; exact hsel
    · exact Subtype.ext (hva'.trans (K.e1_val layer hLayer a1)).symm

theorem capE_mem_selNative (kSel : Fin w → Option ℕ) (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree)
    (hb1 : b1 ∈ capSelT K layer hLayer kSel) :
    capE K layer hLayer b1 ∈ MkSlotsS.selNative D hS layer hLayer J kSel (.inl q) := by
  refine Finset.mem_filter.2 ⟨(capE_selSet K layer hLayer b1 kSel).1 hb1, (K.Dq layer hLayer).ι b1.toNode,
    fun β => native_not_core (q := q) _ β, ?_⟩
  exact K.e1_val layer hLayer b1.toNode |>.symm

include hGeo in
theorem selNative_eq_empty (kSel : Fin w → Option ℕ) (h : capSelT K layer hLayer kSel = ∅) :
    MkSlotsS.selNative D hS layer hLayer J kSel (.inl q) = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
  obtain ⟨b1, hb1, -⟩ := selNative_sub K layer hLayer hGeo kSel v hv
  rw [h] at hb1
  exact Finset.notMem_empty _ hb1

include hGeo in
theorem selNative_eq_single (kSel : Fin w → Option ℕ) (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree)
    (hb1 : b1 ∈ capSelT K layer hLayer kSel) :
    MkSlotsS.selNative D hS layer hLayer J kSel (.inl q) = {capE K layer hLayer b1} := by
  ext v
  rw [Finset.mem_singleton]
  constructor
  · intro hv
    obtain ⟨b1', hb1', rfl⟩ := selNative_sub K layer hLayer hGeo kSel v hv
    rw [capSelT_eq K layer hLayer kSel hb1' hb1]
  · rintro rfl
    exact capE_mem_selNative K layer hLayer kSel b1 hb1

theorem capSelT_single (kSel : Fin w → Option ℕ) (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree)
    (hb1 : b1 ∈ capSelT K layer hLayer kSel) : capSelT K layer hLayer kSel = {b1} := by
  ext b1'
  rw [Finset.mem_singleton]
  exact ⟨fun h => capSelT_eq K layer hLayer kSel h hb1, fun h => h ▸ hb1⟩

/-- A selection on the chain's tree forces a plain pattern there, hence the configuration `term`. -/
theorem cfg_term_of_plain (pat : Fin w → FixPat) (hpat : pat K.u.1 = FixPat.plain) :
    CapP.cfgPat K layer hLayer pat = .term := by
  unfold CapP.cfgPat objCfg
  rw [hpat]
  simp [K.portFlower layer hLayer]

theorem capSel_plain (pat : Fin w → FixPat) (kSel : Fin w → Option ℕ)
    (hplain : ∀ j, (kSel j).isSome → pat j = FixPat.plain) (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree)
    (hb1 : b1 ∈ capSelT K layer hLayer kSel) : pat K.u.1 = FixPat.plain :=
  hplain _ (selSetCap_spec ((capE_selSet K layer hLayer b1 kSel).1 hb1)).1

include hGeo in
/-- **A selected branch of the paired tree is a strict chain node other than the terminal one.** -/
theorem capSel_chain (kSel : Fin w → Option ℕ) (b1 : GBranch (K.Dq layer hLayer).T1.garden.tree)
    (hb1 : b1 ∈ capSelT K layer hLayer kSel) :
    b1.1.2 <+: K.X.lonePath ∧ b1.1.2 ≠ K.X.lonePath ∧ b1.1.2 ≠ K.X.lonePath.dropLast := by
  obtain ⟨h1, h2, h3⟩ := sel_on_chain hGeo (K.capStem layer hLayer) ((capE_selSet K layer hLayer b1 kSel).1 hb1)
    b1.2 rfl
  exact ⟨h1, h2, fun h => h3 ⟨K.portFlower layer hLayer, h⟩⟩

/-! ### `SelAdj` -/

include layer hLayer in
theorem nodes_root_fst (j : Fin 2) :
    ((nativeCoupleForest D hS q).root j).1.1 = K.u.1 ∨ ((nativeCoupleForest D hS q).root j).1.1 = K.cleaf.1.1 := by
  have hne := (K.Dq layer hLayer).ne
  rcases (by decide : ∀ a b c : Fin 2, a ≠ b → c = a ∨ c = b) K.j0 K.c j hne with rfl | rfl
  · left; rw [K.root_j0]; rfl
  · right; rw [K.root_c]; exact inflatedPosition_index S D.tree _

include layer hLayer in
/-- The clock branches of a cap pair are in the chain's tree or in the cap tree. -/
theorem argSrc_fst (i : Fin 2) (β : GBranch S.tree) (h : argSrc hS (.inl q) i = Sum.inr β) :
    β.1.1 = K.u.1 ∨ β.1.1 = K.cleaf.1.1 := by
  fin_cases i
  · have h' : clkOfNode S (q.firstLeaf hS).toNode = Sum.inr β := by simpa [argSrc] using h
    rw [clkOfNode_inr_fst h']
    have := nodes_root_fst K layer hLayer 0
    simpa [nativeCoupleForest, attachedNode, inflatedPosition_index] using this
  · have h' : clkOfNode S (q.secondLeaf hS).toNode = Sum.inr β := by simpa [argSrc] using h
    rw [clkOfNode_inr_fst h']
    have := nodes_root_fst K layer hLayer 1
    simpa [nativeCoupleForest, attachedNode, inflatedPosition_index] using this

/-- **`SelAdj` on a cap pair**: the selected clock is the core of a branch of the chain's tree, the pattern there is
plain, and no branch of the paired tree is selected. -/
theorem selAdj_cap (pat : Fin w → FixPat) (kSel : Fin w → Option ℕ)
    (hplain : ∀ j, (kSel j).isSome → pat j = FixPat.plain)
    (h : MkSlotsI.SelAdj D hS layer hLayer J kSel (.inl q)) :
    pat K.u.1 = FixPat.plain ∧ capSelT K layer hLayer kSel = ∅ := by
  obtain ⟨i, β, hi, v, hv, hvβ⟩ := h
  obtain ⟨hk, -, ⟨ℓ, hℓ, hvℓ⟩, -⟩ := selSetCap_spec hv
  have hvt : v.1.1 = β.1.1 := by rw [hvβ]; exact IntRest.coreBranch_fst D hS β
  have hβu : β.1.1 = K.u.1 := by
    rcases argSrc_fst K layer hLayer i β hi with h1 | h1
    · exact h1
    · exfalso
      have e : ℓ.1.1 = K.cleaf.1.1 := hvℓ.1.symm.trans (hvt.trans h1)
      exact hℓ.1 (by rw [e]; exact K.cJ)
  rw [hvt, hβu] at hk
  refine ⟨hplain _ hk, Finset.eq_empty_of_forall_notMem fun b1 hb1 => ?_⟩
  have he := selSetCap_eq_of_tree ((capE_selSet K layer hLayer b1 kSel).1 hb1) hv (by rw [hvt, hβu]; rfl)
  apply not_capCore K layer hLayer b1
  refine ⟨β, Subtype.ext ?_⟩
  rw [← capE_toNode K layer hLayer b1]
  show (capE K layer hLayer b1).1 = (D.coreBranch hS β).1
  rw [he, hvβ]

/-! ### The lone leaf -/

include hGeo in
theorem capT1_lone_layer (a : GNode (K.Dq layer hLayer).T1.garden.tree) (ha : a.1.2 = K.X.lonePath) :
    (K.Dq layer hLayer).T1.layer a = p := by
  rw [K.capT1_layer layer hLayer a, ha]
  have hf : (addrExt K.u K.X.lonePath).2 ∈
      ((layeredReconstruction D hS layer hLayer).garden.tree (addrExt K.u K.X.lonePath).1).nodes :=
    K.flower.toNode.2
  rw [layerAt_of_mem _ hf]
  exact hGeo.stem_layer _ ⟨K.flower, K.isCapFlower layer hLayer, rfl, List.prefix_refl _⟩

end CapK

end WaveTurbulence.Flower.MkSlotsO
