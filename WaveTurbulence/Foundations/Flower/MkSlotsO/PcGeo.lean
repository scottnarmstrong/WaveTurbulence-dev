/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.PcKer
public import WaveTurbulence.Foundations.Flower.ProtGeo.Cfg
public import WaveTurbulence.Foundations.Flower.ProtGeo.Sel
public import WaveTurbulence.Foundations.Flower.ProtPin.Ambient
public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeo
public import WaveTurbulence.Foundations.Flower.MkSlots.CapNat
public import WaveTurbulence.Foundations.Flower.MkSlotsS.SelGeo

/-! # PROT-CHAIN (`Pc`): the native chain of a stem chain slot is a D3/D6 protected object

For a chain slot `.inr β` of a reconstruction with capped geometry whose core is on the capped stem and whose chain
`X = D.tree β` is not `nil`:

* `pcE`, **`pc_LG_eq`**: the native chain is D2b's `objTree` of the reconstruction;
* **`pc_stemChain`**: the chain is a D2b stem chain; `pc_not_portFlower`: its lone position (the core of `β`) is a
  branch, so `objCfg` is `none`, `root` (a `dRoot` skeleton root) or `term` (`dParent`, the core is a capped flower
  parent, F-H3-3) (`pc_objCfg_cases`);
* `pc_fixN`: the native pins are the pins of `objCfg`; `pc_hlp`: no pinned lone parent has a free lower clock;
* the lone parent (`pc_lonePar`), the core-on-stem test from a native stem node (`pc_core_stem`), the upper clock
  window (`pc_clk0`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Links
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.ProtDefs
  WaveTurbulence.Flower.ProtGeo

namespace WaveTurbulence.Flower.MkSlotsO

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) (β : GBranch S.tree)

/-- The reconstruction. -/
abbrev pcR : LayeredGarden w := layeredReconstruction D hS layer hLayer

/-- The attachment address of the chain of `β`. -/
abbrev pcu : Fin w × Path := inflatedPosition S D.tree β.toNode

/-- The subtree below the lone position. -/
abbrev pcH : TTree := node3 fun i => D.inflateNode hS (β.child i)

theorem pcE : ChainEmb (pcR D hS layer hLayer).garden (D.tree β) (nodeSign S.sig β.1) (pcu D β) (pcH D hS β) :=
  LFTwist.reconstruction_chainEmb D hS (D.garden_decodes hS) β

/-- **The native chain is D2b's `objTree`.** -/
theorem pc_LG_eq : nativeChainLayered D hS layer hLayer β =
    objTree (pcR D hS layer hLayer) (D.tree β) (nodeSign S.sig β.1) (pcu D β) (pcE D hS layer hLayer β) := by
  unfold objTree nativeChainLayered
  congr 1
  funext a
  rw [layerAt_of_mem (z := addrExt (pcu D β) a.1.2) (pcR D hS layer hLayer) (chainContextNode D hS β a).2]
  rfl

theorem pcj_eq : pcj D β = β.1.1 := inflatedPosition_index S D.tree β.toNode

theorem pc_u_nil (h : (pcu D β).2 = []) : β.1.2 = [] := by
  by_contra hne
  have e : (pcu D β).2 = (inflatedPosition S D.tree (β.toNode.parent hne).toNode).2 ++
      ((D.tree (β.toNode.parent hne)).lonePath ++ [β.1.2.getLast hne]) := by
    show (inflatedPosition S D.tree β.toNode).2 = _
    rw [inflatedPosition]
    have hne' : ¬ (β.toNode).1.2 = [] := hne
    simp only [hne', ↓reduceDIte]
    rfl
  rw [e] at h
  simp at h

/-- A non-core node of the native chain witnesses a non-`nil` chain. -/
theorem pc_ne_nil (y : GNode (decodedTree (D.tree β) (nodeSign S.sig β.1)).tree)
    (hy : y.1.2 ≠ (D.tree β).lonePath) : D.tree β ≠ .nil := by
  have key : ∀ (X : RegChain) (q : Path), q ∈ (X.plug (nodeSign S.sig β.1) .leaf).nodes → q ≠ X.lonePath →
      X ≠ .nil := by
    intro X q hq hqn hX
    subst hX
    simp [RegChain.plug, RegChain.lonePath, TTree.nodes] at hq hqn
    exact hqn hq
  exact key _ _ y.2 hy

variable (J : Finset (Fin w))

theorem pc_not_portFlower : ¬ PortFlower (pcR D hS layer hLayer) J (D.tree β) (pcu D β) := by
  rintro ⟨f, -, hf⟩
  have hl := f.2
  have h1 : f.1 = (D.coreBranch hS β).1 := hf
  rw [h1] at hl
  exact Comb.TreePath.not_mem_branching_of_mem_leaves _ hl (D.coreBranch hS β).2

/-- A native stem node off the core puts the core on the stem. -/
theorem pc_core_stem (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf)
    (y : GNode (nativeChainLayered D hS layer hLayer β).garden.tree) (hy : y.1.2 ≠ (D.tree β).lonePath)
    (hst : OnCapStem (pcR D hS layer hLayer) J (chainContextNode D hS β y)) :
    OnCapStem (pcR D hS layer hLayer) J (D.coreBranch hS β).toNode :=
  ((pc_onCapStem_ch D hS layer hLayer J β hcap y hy).1 hst).2

/-- **The chain of a stem chain slot is a D2b stem chain.** -/
theorem pc_stemChain (hne : D.tree β ≠ .nil) (hcs : OnCapStem (pcR D hS layer hLayer) J (D.coreBranch hS β).toNode) :
    StemChain (pcR D hS layer hLayer) J (D.tree β) (nodeSign S.sig β.1) (pcu D β) (pcH D hS β) := by
  have hb : ([] : Path) ∈ ((D.tree β).plug (nodeSign S.sig β.1) .leaf).branching :=
    prefix_lone_branching (D.tree β) (nodeSign S.sig β.1) (List.nil_prefix) (fun h => lonePath_ne_nil hne h.symm)
  obtain ⟨ℓ, hℓ, h1, h2⟩ := hcs
  refine ⟨pcE D hS layer hLayer β, D.tree_wf β, embBr (pcE D hS layer hLayer β) [] hb,
    addrExt_mem_branchAddresses.2 hb, ℓ, hℓ, h1, ?_⟩
  have h2' : (pcu D β).2 ++ (D.tree β).lonePath <+: ℓ.1.2 := h2
  show (pcu D β).2 ++ [] <+: ℓ.1.2
  rw [List.append_nil]
  exact (List.prefix_append _ _).trans h2'

/-- The configuration of a stem chain slot: `none`, `root` or `term`. -/
theorem pc_objCfg_cases (pat : Fin w → FixPat) :
    objCfg (pcR D hS layer hLayer) J pat (D.tree β) (pcu D β) = .none ∨
    (objCfg (pcR D hS layer hLayer) J pat (D.tree β) (pcu D β) = .root ∧ pat (pcj D β) = .dRoot ∧
      (pcu D β).2 = []) ∨
    (objCfg (pcR D hS layer hLayer) J pat (D.tree β) (pcu D β) = .term ∧ pat (pcj D β) = .dParent ∧
      PortFP (pcR D hS layer hLayer) J (D.tree β) (pcu D β)) := by
  have hpf := pc_not_portFlower D hS layer hLayer β J
  unfold objCfg
  cases hp : pat (pcu D β).1 with
  | plain => simp [hpf]
  | dRoot =>
    by_cases hu : (pcu D β).2 = []
    · simp [hpf, hu]
    · simp [hpf, hu]
  | dParent =>
    by_cases hf : PortFP (pcR D hS layer hLayer) J (D.tree β) (pcu D β)
    · simp [hpf, hf]
    · simp [hpf, hf]
  | dChild i => simp [hpf]

/-- **The native pins are the pins of `objCfg`.** -/
theorem pc_fixN {p : ℕ} (hG : CapGeo (pcR D hS layer hLayer) J p)
    (hSt : StemChain (pcR D hS layer hLayer) J (D.tree β) (nodeSign S.sig β.1) (pcu D β) (pcH D hS β))
    (pat : Fin w → FixPat) (t s up : ℝ) (b : GBranch (nativeChainLayered D hS layer hLayer β).garden.tree) :
    fixNative D hS (fixCap (pcR D hS layer hLayer) J pat t s) (.inr β) b =
      (objCfg (pcR D hS layer hLayer) J pat (D.tree β) (pcu D β)).fix (D.tree β) s t up b := by
  have hb : MkSlotsB.nativeBr D hS (.inr β) b = embBr hSt.emb b.1.2 b.2 := Subtype.ext rfl
  show fixCap (pcR D hS layer hLayer) J pat t s (MkSlotsB.nativeBr D hS (.inr β) b) = _
  rw [hb]
  exact fixCap_objTree hG hSt pat t s up b

theorem pc_none_fix (X : RegChain) (s t up : ℝ) {T : Fin 1 → TTree} (b : GBranch T) :
    ProtCfg.none.fix X s t up b = none := by
  unfold ProtCfg.fix
  simp [ProtCfg.pins]

theorem pc_root_fix (X : RegChain) (s t up : ℝ) {T : Fin 1 → TTree} (b : GBranch T) :
    ProtCfg.root.fix X s t up b = if b.1.2 = [] then some t else none := by
  unfold ProtCfg.fix
  have h0 : b.1.1.val = 0 := Fin.val_eq_zero b.1.1
  simp only [h0, ↓reduceIte, ProtCfg.pins, List.lookup]
  by_cases h : b.1.2 = []
  · simp [h]
  · rw [beq_false_of_ne h]
    simp [h]

/-- A lone parent of the native chain is the parent of its lone leaf. -/
theorem pc_lonePar (b : GBranch (nativeChainLayered D hS layer hLayer β).garden.tree)
    (hb : (nativeChainLayered D hS layer hLayer β).garden.IsLoneParent b) :
    b.1.2 = (D.tree β).lonePath.dropLast := by
  obtain ⟨ℓ, hl, -, i, h2⟩ := hb
  have hl' := (decodesTree_lone_iff (decodedTree_decodes (D.tree β) (nodeSign S.sig β.1)) ℓ).1 hl
  rw [← hl', h2, List.dropLast_concat]

/-- **No pinned lone parent has a free lower clock.** -/
theorem pc_hlp {p : ℕ} (hG : CapGeo (pcR D hS layer hLayer) J p) (hne : D.tree β ≠ .nil)
    (hSt : StemChain (pcR D hS layer hLayer) J (D.tree β) (nodeSign S.sig β.1) (pcu D β) (pcH D hS β))
    (pat : Fin w → FixPat) (t s : ℝ) :
    ∀ b, (nativeChainLayered D hS layer hLayer β).garden.IsLoneParent b →
      fixNative D hS (fixCap (pcR D hS layer hLayer) J pat t s) (.inr β) b ≠ none →
      fixCore D hS (fixCap (pcR D hS layer hLayer) J pat t s) β ≠ none := by
  intro b hb hf
  rw [pc_fixN D hS layer hLayer β J hG hSt pat t s 0 b] at hf
  have hlp := pc_lonePar D hS layer hLayer β b hb
  rcases pc_objCfg_cases D hS layer hLayer β J pat with h | ⟨h, -, -⟩ | ⟨h, -, c, hc, hcv⟩
  · rw [h, pc_none_fix] at hf
    exact absurd rfl hf
  · rw [h, pc_root_fix] at hf
    have h0 : b.1.2 = [] := by
      by_contra h0
      simp [h0] at hf
    rw [h0] at hlp
    have := congrArg List.length hlp
    simp only [List.length_nil, List.length_dropLast] at this
    have := two_le_lonePath hne
    omega
  · have hce : c = D.coreBranch hS β := Subtype.ext hcv
    show fixCap (pcR D hS layer hLayer) J pat t s (D.coreBranch hS β) ≠ none
    rw [← hce]
    unfold fixCap
    simp [hc]

/-- The upper clock of a stem chain slot is in layer `p`. -/
theorem pc_clk0 {p : ℕ} (hG : CapGeo (pcR D hS layer hLayer) J p)
    (hcs : OnCapStem (pcR D hS layer hLayer) J (D.coreBranch hS β).toNode) :
    Represents.clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (Represents.argSrc hS (.inr β) 0) = p := by
  have e : Represents.argSrc hS (.inr β) 0 = Represents.clkOfNode S β.toNode := rfl
  rw [e, ← Represents.parentLayer_inflated D hS layer hLayer p β.toNode ⟨pcu D β, (pcE D hS layer hLayer β).node⟩ rfl]
  unfold LayeredGarden.parentLayer
  split_ifs with h
  · rfl
  · obtain ⟨ℓ, hℓ, h1, h2⟩ := hcs
    have h2' : (pcu D β).2 ++ (D.tree β).lonePath <+: ℓ.1.2 := h2
    refine hG.stem_layer _ ⟨ℓ, hℓ, h1, ?_⟩
    show (pcu D β).2.dropLast <+: ℓ.1.2
    exact (List.dropLast_prefix _).trans ((List.prefix_append _ _).trans h2')

end WaveTurbulence.Flower.MkSlotsO
