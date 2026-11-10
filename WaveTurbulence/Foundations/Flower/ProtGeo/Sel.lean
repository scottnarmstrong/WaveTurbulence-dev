/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtGeo.Cfg

/-! # D2b PROT-GEO (6): item (iii), selected vertices of a protected object

The intrinsic selected vertices `selSetCap LG J kSel` (one per tree, on the capped stem, never a flower parent):
* `sel_on_chain`: a selected branching vertex of a stem chain is a chain node (a strict prefix of the lone path), and
  not the terminal node when the lone leaf is the capped flower;
* `sel_fixCap_none` (with F-D0-8's `hplain`): it is unpinned;
* `objCfg_of_sel`: an object containing a selected vertex has configuration `none` or `term`;
* `card_sel_le_one`: an object contains at most one selected vertex.
Extraction forms in D6's (`ProtAnnBoundAt`, `RegularComponentPointwiseAt`) shape: `objSelT`, `objSelC`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Flower.MkDefs
  WaveTurbulence.Flower.ProtDefs

namespace WaveTurbulence.Flower.ProtGeo

variable {w : ℕ} {LG : LayeredGarden w} {J : Finset (Fin w)} {p : ℕ} {X : RegChain} {ζ : ℤˣ}
  {u : Fin w × Path} {h : TTree}

/-! ## The intrinsic selection -/

theorem stemAt_spec {j : Fin w} {k : ℕ} {b : GBranch LG.garden.tree} (h : stemAt LG J j k = some b) :
    b ∈ stemSetCap LG J j := by
  unfold stemAt at h
  split_ifs at h with hc
  have hs := Classical.choose_spec (Finset.card_eq_one.mp hc)
  have hm := (Finset.eq_singleton_iff_unique_mem.mp hs).1
  rw [← Option.some.inj h]
  exact (Finset.mem_filter.mp hm).1

theorem selCap_spec {kSel : Fin w → Option ℕ} {j : Fin w} {b : GBranch LG.garden.tree}
    (h : selCap LG J kSel j = some b) : (kSel j).isSome ∧ b ∈ stemSetCap LG J j := by
  unfold selCap at h
  cases hk : kSel j with
  | none => rw [hk] at h; simp at h
  | some k => rw [hk] at h; exact ⟨rfl, stemAt_spec h⟩

theorem mem_stemSetCap {j : Fin w} {b : GBranch LG.garden.tree} :
    b ∈ stemSetCap LG J j ↔ b.1.1 = j ∧ OnCapStem LG J b.toNode ∧ ¬ IsCapFlowerParent LG J b := by
  unfold stemSetCap; simp

/-- A selected vertex: its tree has a selection, it is a capped stem node, not a flower parent. -/
theorem selSetCap_spec {kSel : Fin w → Option ℕ} {b : GBranch LG.garden.tree} (hb : b ∈ selSetCap LG J kSel) :
    (kSel b.1.1).isSome ∧ selCap LG J kSel b.1.1 = some b ∧ OnCapStem LG J b.toNode ∧
      ¬ IsCapFlowerParent LG J b := by
  unfold selSetCap at hb
  obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hb).2
  obtain ⟨hk, hs⟩ := selCap_spec hj
  obtain ⟨hbj, hon, hnf⟩ := mem_stemSetCap.mp hs
  subst hbj
  exact ⟨hk, hj, hon, hnf⟩

/-- At most one selected vertex per tree. -/
theorem selSetCap_eq_of_tree {kSel : Fin w → Option ℕ} {b b' : GBranch LG.garden.tree}
    (hb : b ∈ selSetCap LG J kSel) (hb' : b' ∈ selSetCap LG J kSel) (h : b.1.1 = b'.1.1) : b = b' := by
  have e1 := (selSetCap_spec hb).2.1
  have e2 := (selSetCap_spec hb').2.1
  rw [h] at e1
  exact Option.some.inj (e1.symm.trans e2)

/-- **(iii) unpinned** (F-D0-8): with `pat j = plain` on selected trees, a selected vertex carries no pin. -/
theorem sel_fixCap_none {pat : Fin w → FixPat} {kSel : Fin w → Option ℕ}
    (hplain : ∀ j, (kSel j).isSome → pat j = FixPat.plain) (t s : ℝ) {b : GBranch LG.garden.tree}
    (hb : b ∈ selSetCap LG J kSel) : fixCap LG J pat t s b = none := by
  obtain ⟨hk, -, -, hnf⟩ := selSetCap_spec hb
  unfold fixCap
  rw [ite_eq_right hnf, hplain _ hk]

/-! ## Selected vertices of a stem chain -/

/-- **(iii) on the chain.** A selected branching vertex of a stem chain is a chain node, and not the terminal node
when the lone leaf is the capped flower. -/
theorem sel_on_chain (hG : CapGeo LG J p) (hS : StemChain LG J X ζ u h) {kSel : Fin w → Option ℕ}
    {b : GBranch LG.garden.tree} (hb : b ∈ selSetCap LG J kSel) {q : Path}
    (hq : q ∈ (X.plug ζ .leaf).branching) (hbq : b.1 = addrExt u q) :
    q <+: X.lonePath ∧ q ≠ X.lonePath ∧ ¬ (PortFlower LG J X u ∧ q = X.lonePath.dropLast) := by
  obtain ⟨-, -, ⟨f, hf, hbf⟩, hnf⟩ := selSetCap_spec hb
  have hU : Under (addrExt u q) f.1 := ⟨by rw [← hbq]; exact hbf.1, by rw [← hbq]; exact hbf.2⟩
  obtain ⟨h1, h2⟩ := branch_lt_lone hG.cap_leaf hS.emb hq hf hU
  exact ⟨h1, h2, fun h' => hnf ((fp_iff hG hS hq hbq).mpr h')⟩

/-- An object containing a selected vertex has a plain pattern, hence configuration `none` or `term`. -/
theorem objCfg_of_sel {pat : Fin w → FixPat} {kSel : Fin w → Option ℕ}
    (hplain : ∀ j, (kSel j).isSome → pat j = FixPat.plain) {b : GBranch LG.garden.tree}
    (hb : b ∈ selSetCap LG J kSel) (hbu : b.1.1 = u.1) :
    objCfg LG J pat X u = if PortFlower LG J X u then .term else .none := by
  have hp := hplain _ (selSetCap_spec hb).1
  rw [hbu] at hp
  simp only [objCfg, hp]

/-! ## Extraction forms (the `Sel` sets of D6) -/

/-- The selected vertices of a paired-tree object, in its own coordinates. -/
def objSelT (hE : ChainEmb LG.garden X ζ u h) (kSel : Fin w → Option ℕ) :
    Finset (GBranch (objTree LG X ζ u hE).garden.tree) :=
  Finset.univ.filter fun b' => embBr hE b'.1.2 b'.2 ∈ selSetCap LG J kSel

/-- **(iii), paired trees, D6 shape.** -/
theorem objSelT_spec (hG : CapGeo LG J p) (hS : StemChain LG J X ζ u h) {pat : Fin w → FixPat}
    {kSel : Fin w → Option ℕ} (hplain : ∀ j, (kSel j).isSome → pat j = FixPat.plain) (t s up : ℝ) :
    ∀ b' ∈ objSelT (J := J) hS.emb kSel, b'.1.1.val = 0 ∧ b'.1.2 <+: X.lonePath ∧ b'.1.2 ≠ X.lonePath ∧
      (objCfg LG J pat X u = .term → b'.1.2 ≠ X.lonePath.dropLast) ∧
      (objCfg LG J pat X u).fix X s t up b' = none := by
  intro b' hb'
  have hsel := (Finset.mem_filter.mp hb').2
  obtain ⟨h1, h2, h3⟩ := sel_on_chain hG hS hsel b'.2 rfl
  refine ⟨Fin.val_eq_zero _, h1, h2, fun hc he => h3 ⟨?_, he⟩, ?_⟩
  · rw [objCfg_of_sel (X := X) (u := u) hplain hsel rfl] at hc
    by_contra hpf; rw [ite_eq_right hpf] at hc; cases hc
  · rw [← fixCap_objTree hG hS pat t s up b']
    exact sel_fixCap_none hplain t s hsel

theorem objSelT_card (hE : ChainEmb LG.garden X ζ u h) (kSel : Fin w → Option ℕ) :
    (objSelT (J := J) hE kSel).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro b hb b' hb'
  have e := selSetCap_eq_of_tree (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hb').2 rfl
  have e2 : b.1.2 = b'.1.2 := by
    have := congrArg (fun x : GBranch LG.garden.tree => x.1) e
    exact addrExt_injective u this
  exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) e2)

end WaveTurbulence.Flower.ProtGeo
