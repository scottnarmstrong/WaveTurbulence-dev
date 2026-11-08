/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.SlotObl
public import WaveTurbulence.Foundations.Flower.MkSlotsS.SelClass

/-! # B3s-HELPER7 WP6 (R-slot, part 0): the general slot kernel as a kernel of its native object

The general slot kernel `MkSlotsB.slotFnGWFRL … (genΘs …) … fixG` of a slot is β's relaxed weighted node kernel
`kernelNodeWR` of the native layered object of the slot (couple: `nativeCoupleLayered`, chain:
`nativeChainLayered`), with node data read at the native nodes: the leaf profile, the node weight, the per-node factor
of `genΘs`, the native pins, and (chain) the clock pin status.

* `kerC`, `kerT`: these kernels as functions of a layered couple / chain and node data on it;
* `slotFnGWFRL_inl_eq`, `slotFnGWFRL_inr_eq` (definitional);
* **`kerC_transport`**, **`kerT_transport`**: two such kernels agree when the native objects are equal and the node
  data agree at every address (no dependent rewriting needed by the caller);
* `node_fun_congr`, `branch_fun_congr`: functions of a layered garden and a node agree at equal gardens and equal
  addresses;
* **`genNW_nf`** (one capped flower per tree): the stem node weight at a branch `B` is read from four data:
  `B` is on the capped stem and not a capped flower parent, its tree, its depth, and whether its tree has a
  selected vertex; `genNW_noFilt`: without stem filters and selections it is `1`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs

namespace WaveTurbulence.Flower.MkSlotsI

/-! ## The kernels of a layered native object -/

section Ker

variable {d : ℕ}

/-- **The couple kernel** of a layered couple `N` with node data: profiles `Hn`, node weights `Wn`, per-node factors
`Θn` (read at the native resonance), pins `Fn`. -/
def kerC (L γ δ : ℝ) (N : LayeredGarden 2) (Hn : GNode N.garden.tree → Mom d → ℝ)
    (Wn : GNode N.garden.tree → Mom d → ℂ) (Θn : GNode N.garden.tree → ℝ → ℂ)
    (Fn : GBranch N.garden.tree → Option ℝ) (ts : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  MkSlotsB.kernelNodeWR L γ δ N Hn (fun k' => ∏ a, Wn a (k' a))
    (MkSlotsB.kDomainR N (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 Fn (fun _ => False) False)
    k (fun _ => 0) 0 (fun κ => ∏ a, Θn a (MkSlotsS.omegaAt (cosetDecoration N.garden L k κ.1) a)) Fn

/-- **The chain kernel** of a layered chain `N` with node data and the clock pin status `clk`. -/
def kerT (L γ δ : ℝ) (N : LayeredGarden 1) (Hn : GNode N.garden.tree → Mom d → ℝ)
    (Wn : GNode N.garden.tree → Mom d → ℂ) (Θn : GNode N.garden.tree → ℝ → ℂ)
    (Fn : GBranch N.garden.tree → Option ℝ) (clk : Prop) (ts : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  MkSlotsB.kernelNodeWR L γ δ N Hn (fun k' => ∏ a, Wn a (k' a))
    (MkSlotsB.kDomainR N (fun _ => ts 0) (ts 1) Fn (fun _ => False) clk)
    k (fun _ => 0) 0 (fun κ => ∏ a, Θn a (MkSlotsS.omegaAt (cosetDecoration N.garden L k κ.1) a)) Fn

/-- **Transport of the couple kernel**: equal layered couples, node data agreeing at every address. -/
theorem kerC_transport (L γ δ : ℝ) {N₁ N₂ : LayeredGarden 2} (hN : N₁ = N₂)
    {Hn₁ : GNode N₁.garden.tree → Mom d → ℝ} {Hn₂ : GNode N₂.garden.tree → Mom d → ℝ}
    {Wn₁ : GNode N₁.garden.tree → Mom d → ℂ} {Wn₂ : GNode N₂.garden.tree → Mom d → ℂ}
    {Θn₁ : GNode N₁.garden.tree → ℝ → ℂ} {Θn₂ : GNode N₂.garden.tree → ℝ → ℂ}
    {Fn₁ : GBranch N₁.garden.tree → Option ℝ} {Fn₂ : GBranch N₂.garden.tree → Option ℝ}
    (hH : ∀ (x : Fin 2 × Path) (h₁ : x.2 ∈ (N₁.garden.tree x.1).nodes) (h₂ : x.2 ∈ (N₂.garden.tree x.1).nodes),
      Hn₁ ⟨x, h₁⟩ = Hn₂ ⟨x, h₂⟩)
    (hW : ∀ (x : Fin 2 × Path) (h₁ : x.2 ∈ (N₁.garden.tree x.1).nodes) (h₂ : x.2 ∈ (N₂.garden.tree x.1).nodes),
      Wn₁ ⟨x, h₁⟩ = Wn₂ ⟨x, h₂⟩)
    (hΘ : ∀ (x : Fin 2 × Path) (h₁ : x.2 ∈ (N₁.garden.tree x.1).nodes) (h₂ : x.2 ∈ (N₂.garden.tree x.1).nodes),
      Θn₁ ⟨x, h₁⟩ = Θn₂ ⟨x, h₂⟩)
    (hF : ∀ (x : Fin 2 × Path) (h₁ : x.2 ∈ (N₁.garden.tree x.1).branching)
      (h₂ : x.2 ∈ (N₂.garden.tree x.1).branching), Fn₁ ⟨x, h₁⟩ = Fn₂ ⟨x, h₂⟩)
    (ts : Fin 2 → ℝ) (k : Mom d) :
    kerC L γ δ N₁ Hn₁ Wn₁ Θn₁ Fn₁ ts k = kerC L γ δ N₂ Hn₂ Wn₂ Θn₂ Fn₂ ts k := by
  subst hN
  have e1 : Hn₁ = Hn₂ := funext fun a => hH a.1 a.2 a.2
  have e2 : Wn₁ = Wn₂ := funext fun a => hW a.1 a.2 a.2
  have e3 : Θn₁ = Θn₂ := funext fun a => hΘ a.1 a.2 a.2
  have e4 : Fn₁ = Fn₂ := funext fun b => hF b.1 b.2 b.2
  subst e1 e2 e3 e4
  rfl

/-- **Transport of the chain kernel.** -/
theorem kerT_transport (L γ δ : ℝ) {N₁ N₂ : LayeredGarden 1} (hN : N₁ = N₂)
    {Hn₁ : GNode N₁.garden.tree → Mom d → ℝ} {Hn₂ : GNode N₂.garden.tree → Mom d → ℝ}
    {Wn₁ : GNode N₁.garden.tree → Mom d → ℂ} {Wn₂ : GNode N₂.garden.tree → Mom d → ℂ}
    {Θn₁ : GNode N₁.garden.tree → ℝ → ℂ} {Θn₂ : GNode N₂.garden.tree → ℝ → ℂ}
    {Fn₁ : GBranch N₁.garden.tree → Option ℝ} {Fn₂ : GBranch N₂.garden.tree → Option ℝ} {c₁ c₂ : Prop}
    (hH : ∀ (x : Fin 1 × Path) (h₁ : x.2 ∈ (N₁.garden.tree x.1).nodes) (h₂ : x.2 ∈ (N₂.garden.tree x.1).nodes),
      Hn₁ ⟨x, h₁⟩ = Hn₂ ⟨x, h₂⟩)
    (hW : ∀ (x : Fin 1 × Path) (h₁ : x.2 ∈ (N₁.garden.tree x.1).nodes) (h₂ : x.2 ∈ (N₂.garden.tree x.1).nodes),
      Wn₁ ⟨x, h₁⟩ = Wn₂ ⟨x, h₂⟩)
    (hΘ : ∀ (x : Fin 1 × Path) (h₁ : x.2 ∈ (N₁.garden.tree x.1).nodes) (h₂ : x.2 ∈ (N₂.garden.tree x.1).nodes),
      Θn₁ ⟨x, h₁⟩ = Θn₂ ⟨x, h₂⟩)
    (hF : ∀ (x : Fin 1 × Path) (h₁ : x.2 ∈ (N₁.garden.tree x.1).branching)
      (h₂ : x.2 ∈ (N₂.garden.tree x.1).branching), Fn₁ ⟨x, h₁⟩ = Fn₂ ⟨x, h₂⟩)
    (hc : c₁ = c₂) (ts : Fin 2 → ℝ) (k : Mom d) :
    kerT L γ δ N₁ Hn₁ Wn₁ Θn₁ Fn₁ c₁ ts k = kerT L γ δ N₂ Hn₂ Wn₂ Θn₂ Fn₂ c₂ ts k := by
  subst hN hc
  have e1 : Hn₁ = Hn₂ := funext fun a => hH a.1 a.2 a.2
  have e2 : Wn₁ = Wn₂ := funext fun a => hW a.1 a.2 a.2
  have e3 : Θn₁ = Θn₂ := funext fun a => hΘ a.1 a.2 a.2
  have e4 : Fn₁ = Fn₂ := funext fun b => hF b.1 b.2 b.2
  subst e1 e2 e3 e4
  rfl

/-- Functions of a layered garden and of one of its nodes agree at equal gardens and equal addresses. -/
theorem node_fun_congr {n : ℕ} {β : Type*} (F : (N : LayeredGarden n) → GNode N.garden.tree → β)
    {N₁ N₂ : LayeredGarden n} (hN : N₁ = N₂) (x : Fin n × Path) (h₁ : x.2 ∈ (N₁.garden.tree x.1).nodes)
    (h₂ : x.2 ∈ (N₂.garden.tree x.1).nodes) : F N₁ ⟨x, h₁⟩ = F N₂ ⟨x, h₂⟩ := by
  subst hN
  rfl

/-- Functions of a layered garden and of one of its branches agree at equal gardens and equal addresses. -/
theorem branch_fun_congr {n : ℕ} {β : Type*} (F : (N : LayeredGarden n) → GBranch N.garden.tree → β)
    {N₁ N₂ : LayeredGarden n} (hN : N₁ = N₂) (x : Fin n × Path) (h₁ : x.2 ∈ (N₁.garden.tree x.1).branching)
    (h₂ : x.2 ∈ (N₂.garden.tree x.1).branching) : F N₁ ⟨x, h₁⟩ = F N₂ ⟨x, h₂⟩ := by
  subst hN
  rfl

/-- Node membership transfers along equal layered gardens. -/
theorem nodes_of_eq {n : ℕ} {N₁ N₂ : LayeredGarden n} (hN : N₁ = N₂) {x : Fin n × Path}
    (h : x.2 ∈ (N₁.garden.tree x.1).nodes) : x.2 ∈ (N₂.garden.tree x.1).nodes := hN ▸ h

theorem branching_of_eq {n : ℕ} {N₁ N₂ : LayeredGarden n} (hN : N₁ = N₂) {x : Fin n × Path}
    (h : x.2 ∈ (N₁.garden.tree x.1).branching) : x.2 ∈ (N₂.garden.tree x.1).branching := hN ▸ h

end Ker

/-! ## The general slot kernel as a native kernel -/

section Slot

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)

/-- The per-node factor of `genΘs` at a node of the reconstruction: `1` at a core node, the stem node weight
elsewhere. -/
def genNode (z : GNode (D.forest hS)) (v : ℝ) : ℂ :=
  if ∃ β : GBranch S.tree, z = (D.coreBranch hS β).toNode then 1
  else genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs z v

theorem slotFnGWFRL_inl_eq (γ δ : ℝ) (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (fixG : GBranch (D.forest hS) → Option ℝ) (p : SourcePair S) (ts : Fin 2 → ℝ) (k : Mom d) :
    MkSlotsB.slotFnGWFRL D hS L γ δ H W (genΘs D hS layer hLayer J L σ kSel Rs) layer hLayer fixG (.inl p) ts k =
      kerC L γ δ (nativeCoupleLayered D hS layer hLayer p)
        (fun a => H ((nativeCoupleForest D hS p).nodeEmbedding a).1)
        (fun a => W ((nativeCoupleForest D hS p).nodeEmbedding a))
        (fun a => genNode D hS layer hLayer J L σ kSel Rs ((nativeCoupleForest D hS p).nodeEmbedding a))
        (MkSlots.fixNative D hS fixG (.inl p)) ts k := rfl

theorem slotFnGWFRL_inr_eq (γ δ : ℝ) (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (fixG : GBranch (D.forest hS) → Option ℝ) (b : GBranch S.tree) (ts : Fin 2 → ℝ) (k : Mom d) :
    MkSlotsB.slotFnGWFRL D hS L γ δ H W (genΘs D hS layer hLayer J L σ kSel Rs) layer hLayer fixG (.inr b) ts k =
      kerT L γ δ (nativeChainLayered D hS layer hLayer b)
        (fun a => H (chainContextNode D hS b a).1)
        (fun a => W (chainContextNode D hS b a))
        (fun a => genNode D hS layer hLayer J L σ kSel Rs (chainContextNode D hS b a))
        (MkSlots.fixNative D hS fixG (.inr b)) (MkSlots.fixCore D hS fixG b = none) ts k := rfl

end Slot

/-! ## The stem node weight in normal form -/

section NF

variable {w : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ)
  (Rs : Fin w → ℝ)

/-- The stem node weight on non-branches. -/
theorem genNW_not_branch (z : GNode LG.garden.tree) (hz : z.1.2 ∉ (LG.garden.tree z.1.1).branching) (x : ℝ) :
    genNW LG J L σ kSel Rs z x = 1 := by
  unfold genNW
  rw [dif_neg hz]

/-- Without stem filters and selections the stem node weight is `1`. -/
theorem genNW_noFilt (Rs : Fin w → ℝ) (z : GNode LG.garden.tree) (x : ℝ) :
    genNW LG J L (fun _ => none) (fun _ => none) Rs z x = 1 := by
  unfold genNW
  split_ifs with h1 h2 h3
  · exfalso
    obtain ⟨j, hj⟩ := (Finset.mem_filter.1 h3).2
    simp [selCap] at hj
  · have e1 : MkSlotsT.radSigma L (fun _ => none) (⟨z.1, h1⟩ : GBranch LG.garden.tree) = [] := rfl
    have e2 : MkSlotsG.shellRad LG J (fun _ => none) Rs (⟨z.1, h1⟩ : GBranch LG.garden.tree) = [] := by
      unfold MkSlotsG.shellRad
      rw [if_neg]
      rintro ⟨v, hv, -⟩
      simp [selCap] at hv
    simp [MkSlotsG.radRaw, e1, e2, MkSlotsT.radProd]
  · rfl
  · rfl

/-- The stem node weight at a branch (unfolded). -/
theorem genNW_br (B : GBranch LG.garden.tree) (x : ℝ) :
    genNW LG J L σ kSel Rs B.toNode x =
      if ∃ j, B ∈ stemSetCap LG J j then
        (MkSlotsT.radProd (MkSlotsG.radRaw LG J L σ kSel Rs B) x : ℂ) *
          (if B ∈ selSetCap LG J kSel then ((chiD (|x| / Rs B.1.1) : ℝ) : ℂ) else 1)
      else 1 := by
  have hb : (B.toNode).1.2 ∈ (LG.garden.tree (B.toNode).1.1).branching := B.2
  have he : (⟨(B.toNode).1, hb⟩ : GBranch LG.garden.tree) = B := rfl
  unfold genNW
  rw [dite_eq_left hb, he]
  split_ifs <;> first | rfl | contradiction

variable {LG J}

/-- **The stem node weight at a branch, in normal form** (one capped flower per tree). -/
theorem genNW_nf (hone : MkSlotsS.OneFlower LG J) (B : GBranch LG.garden.tree) (v : ℝ) :
    genNW LG J L σ kSel Rs B.toNode v =
      if OnCapStem LG J B.toNode ∧ ¬ IsCapFlowerParent LG J B then
        (MkSlotsT.radProd (MkSlotsT.radSigma L σ B ++
          (if (selCap LG J kSel B.1.1).isSome ∧ kSel B.1.1 ≠ some B.1.2.length then [Rs B.1.1] else [])) v : ℂ) *
        (if kSel B.1.1 = some B.1.2.length then ((chiD (|v| / Rs B.1.1) : ℝ) : ℂ) else 1)
      else 1 := by
  have hstem : (∃ j, B ∈ stemSetCap LG J j) ↔ OnCapStem LG J B.toNode ∧ ¬ IsCapFlowerParent LG J B := by
    constructor
    · rintro ⟨j, hj⟩
      exact (MkSlotsS.mem_stemSetCap_iff'.1 hj).2
    · intro h
      exact ⟨B.1.1, MkSlotsS.mem_stemSetCap_iff'.2 ⟨rfl, h⟩⟩
  rw [genNW_br]
  by_cases hs : OnCapStem LG J B.toNode ∧ ¬ IsCapFlowerParent LG J B
  · have hst : B ∈ stemSetCap LG J B.1.1 := MkSlotsS.mem_stemSetCap_iff'.2 ⟨rfl, hs⟩
    rw [if_pos (hstem.2 hs), if_pos hs]
    have hsel : B ∈ selSetCap LG J kSel ↔ kSel B.1.1 = some B.1.2.length := by
      constructor
      · intro h
        exact ((MkSlotsS.selCap_eq_some_iff hone kSel _ B).1 (MkSlotsS.selCap_of_mem_selSetCap h)).2
      · intro h
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, B.1.1, ?_⟩
        exact (MkSlotsS.selCap_eq_some_iff hone kSel _ B).2 ⟨hst, h⟩
    have hshell : MkSlotsG.shellRad LG J kSel Rs B =
        if (selCap LG J kSel B.1.1).isSome ∧ kSel B.1.1 ≠ some B.1.2.length then [Rs B.1.1] else [] := by
      unfold MkSlotsG.shellRad
      congr 1
      apply propext
      constructor
      · rintro ⟨v', hv', hne⟩
        refine ⟨by rw [hv']; rfl, fun hk => hne ?_⟩
        have hv'' := (MkSlotsS.selCap_eq_some_iff hone kSel _ v').1 hv'
        have hl : v'.1.2.length = B.1.2.length := by
          have := hv''.2.symm.trans hk
          exact Option.some.inj this
        exact MkSlotsS.stem_eq_of_length hone hv''.1 hst hl
      · rintro ⟨hsome, hk⟩
        obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.1 hsome
        refine ⟨v', hv', fun he => hk ?_⟩
        rw [he] at hv'
        exact ((MkSlotsS.selCap_eq_some_iff hone kSel _ B).1 hv').2
    unfold MkSlotsG.radRaw
    rw [hshell]
    by_cases hk : kSel B.1.1 = some B.1.2.length
    · rw [if_pos (hsel.2 hk), if_pos hk]
    · rw [if_neg (fun h => hk (hsel.1 h)), if_neg hk]
  · rw [if_neg (fun h => hs (hstem.1 h)), if_neg hs]

end NF

end WaveTurbulence.Flower.MkSlotsI
