/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.PcCh
public import WaveTurbulence.Foundations.Flower.MkSlotsB.CapPKer
public import WaveTurbulence.Foundations.Flower.MkSlots.CapMul3
public import WaveTurbulence.Foundations.Flower.ProtWhole.RegWeight

/-! # PROT-CHAIN (`Pc`): the general slot kernel of a chain slot is a protected kernel of its native chain

On a chain slot `.inr β`, β's relaxed weighted slot kernel `MkSlotsB.slotFnGWFRL` is a `kernelNodeWR` on the relaxed
domain `kDomainR … (fun _ => False) (fixCore β = none)`. When every pinned lone parent of the native chain has a
pinned lower clock (the core of `β`), this domain is D2a's `protDom` (`pc_kDomainR_eq_protDom`), and the weighted node
kernel is D2a's `kernelProt` with the decoration weight moved into the multiplier (`pc_kernelNodeWR_eq_kernelProt`).

* **`pc_slotFn_eq_kernelProt`**: the identification;
* `pc_frontS`, **`pc_fw_prod`**: the frontier node weights of the native chain are INC-TOP's star weight;
* `pcΘ`, **`pcΘ_eq`**: the per-slot factor `genΘs` on a chain is the product of the σ filters `pcFσ`, the
  selection shells `pcFsh` and the selected filters `pcFsel` (`chiD`) over the branches of the native chain;
* `pc_norm_filtWeight_le`: a two-valued filter weight is bounded by `chiDNorm ^ #F`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open MeasureTheory
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.ProtDefs
open WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine

namespace WaveTurbulence.Flower.MkSlotsO

variable {w d : ℕ}

/-! ## The relaxed domain and the bridge -/

/-- **The relaxed chain domain is `protDom`** when no pinned lone parent has a free lower clock. -/
theorem pc_kDomainR_eq_protDom (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (sFree : Prop)
    (h : ∀ b, LG.garden.IsLoneParent b → fix b ≠ none → ¬ sFree) :
    MkSlotsB.kDomainR LG up s fix (fun _ => False) sFree = ProtCut.protDom LG up s fix := by
  ext τ
  simp only [MkSlotsB.kDomainR, ProtCut.protDom, kDomainFix, Set.mem_inter_iff, Set.mem_ofPred_eq, or_false]
  constructor
  · intro hτ
    refine ⟨fun b => ⟨fun hb => ⟨((hτ b).1 hb).1, ((hτ b).1 hb).2.1, ((hτ b).1 hb).2.2, (hτ b).2.1 hb⟩,
      fun b' hb' hf => (hτ b).2.2.1 b' hb' hf⟩, fun b hb hf => (hτ b).2.2.2 hb (Or.inl hf)⟩
  · rintro ⟨h1, h2⟩ b
    refine ⟨fun hb => ⟨((h1 b).1 hb).1, ((h1 b).1 hb).2.1, ((h1 b).1 hb).2.2.1⟩, fun hb => ((h1 b).1 hb).2.2.2,
      fun b' hb' hf => (h1 b).2 b' hb' hf, fun hl hf => ?_⟩
    by_cases hfb : fix b = none
    · exact h2 b hl hfb
    · exact absurd (hf.resolve_left hfb) (h b hl hfb)

/-- **A weighted node kernel on `protDom` is the protected kernel**, the decoration weight (a function of the coset
decoration) moved into the multiplier. -/
theorem pc_kernelNodeWR_eq_kernelProt (L γ δ : ℝ) (LG : LayeredGarden w) (A : GNode LG.garden.tree → Mom d → ℝ)
    (m Θ : (GNode LG.garden.tree → Mom d) → ℂ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) (fix : GBranch LG.garden.tree → Option ℝ) :
    MkSlotsB.kernelNodeWR L γ δ LG A m (ProtCut.protDom LG up s fix) k₀ nroot nfl
        (fun κ => Θ (cosetDecoration LG.garden L k₀ κ.1)) fix =
      kernelProt L γ δ LG (capProfiles LG A) (fun K => m K * Θ K) up s fix k₀ nroot nfl := by
  rw [ProtCut.kernelProt_eq_tsum]
  unfold MkSlotsB.kernelNodeWR
  congr 1
  refine tsum_congr fun κ => ?_
  unfold ProtCut.protSummand ProtCut.protTime
  congr 1
  congr 1
  · congr 1
    rw [integral_fixMeasure]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    dsimp only
    rw [← capExtendFix_eq]
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    rw [capProfiles_leaf]

section Slot

variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) (β : GBranch S.tree)

/-- **The general slot kernel of a chain slot is a protected kernel of its native chain**, when no pinned lone
parent of the chain has a free lower clock. -/
theorem pc_slotFn_eq_kernelProt (L γ δ : ℝ) (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (Θs : (s : ReplacementSlot S) → Mom d → NativeRelativeDecoration D hS d s → ℂ)
    (fixG : GBranch (D.forest hS) → Option ℝ)
    (Θ : (GNode (nativeChainLayered D hS layer hLayer β).garden.tree → Mom d) → ℂ) (ts : Fin 2 → ℝ) (k : Mom d)
    (hΘ : ∀ κ, Θs (.inr β) k κ = Θ (cosetDecoration (nativeChainLayered D hS layer hLayer β).garden L k κ.1))
    (hlp : ∀ b, (nativeChainLayered D hS layer hLayer β).garden.IsLoneParent b →
      fixNative D hS fixG (.inr β) b ≠ none → fixCore D hS fixG β ≠ none) :
    MkSlotsB.slotFnGWFRL D hS L γ δ H W Θs layer hLayer fixG (.inr β) ts k =
      kernelProt L γ δ (nativeChainLayered D hS layer hLayer β)
        (capProfiles (nativeChainLayered D hS layer hLayer β) (fun a => H (chainContextNode D hS β a).1))
        (fun K => (∏ a, W (chainContextNode D hS β a) (K a)) * Θ K) (fun _ => ts 0) (ts 1)
        (fixNative D hS fixG (.inr β)) k (fun _ => 0) 0 := by
  show MkSlotsB.kernelNodeWR L γ δ (nativeChainLayered D hS layer hLayer β)
      (fun a => H (chainContextNode D hS β a).1)
      (fun k' => ∏ a, W (chainContextNode D hS β a) (k' a))
      (MkSlotsB.kDomainR (nativeChainLayered D hS layer hLayer β) (fun _ => ts 0) (ts 1)
        (fixNative D hS fixG (.inr β)) (fun _ => False) (fixCore D hS fixG β = none))
      k (fun _ => 0) 0 (Θs (.inr β) k) (fixNative D hS fixG (.inr β)) = _
  rw [pc_kDomainR_eq_protDom _ _ _ _ _ (fun b hb hf hs => hlp b hb hf hs)]
  have e : Θs (.inr β) k = fun κ => Θ (cosetDecoration (nativeChainLayered D hS layer hLayer β).garden L k κ.1) :=
    funext hΘ
  rw [e]
  exact pc_kernelNodeWR_eq_kernelProt L γ δ _ _ _ Θ _ _ k _ _ _

/-! ## The frontier weight is a star weight -/

/-- The frontier nodes of the native chain. -/
def pc_frontS (p : ℕ) : Finset (GNode (nativeChainLayered D hS layer hLayer β).garden.tree) :=
  Finset.univ.filter fun a => (chainContextNode D hS β a).1.2 ≠ [] ∧
    (layeredReconstruction D hS layer hLayer).layer (chainContextNode D hS β a) < p ∧
    (layeredReconstruction D hS layer hLayer).parentLayer p (chainContextNode D hS β a) = p

/-- The frontier cutoff of the chain's tree. -/
abbrev pc_ω (Rf : Fin w → Option ℝ) :
    GNode (nativeChainLayered D hS layer hLayer β).garden.tree → IncTop.Star d → ℂ :=
  IncTop.topStar (fun _ => frontierG (Rf (inflatedPosition S D.tree β.toNode).1))

theorem pc_fw_prod (p : ℕ) (Rf : Fin w → Option ℝ)
    (K : GNode (nativeChainLayered D hS layer hLayer β).garden.tree → Mom d) :
    ∏ a : GNode (nativeChainLayered D hS layer hLayer β).garden.tree,
        fwNode (layeredReconstruction D hS layer hLayer) p (fun j => frontierG (Rf j)) (chainContextNode D hS β a)
        (K a) =
      IncTop.starWeight (pc_frontS D hS layer hLayer β p) (pc_ω D hS layer hLayer β Rf) K := by
  unfold IncTop.starWeight pc_frontS
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun a _ => ?_
  have hst : pc_ω D hS layer hLayer β Rf a (IncTop.starMomenta K a) =
      frontierG (Rf (inflatedPosition S D.tree β.toNode).1) (K a) := by
    show frontierG (Rf (inflatedPosition S D.tree β.toNode).1) (IncTop.starMomenta K a 0) = _
    rw [IncTop.starMomenta_zero]
  rw [hst]
  unfold fwNode topPsi
  have e1 : (chainContextNode D hS β a).1.1 = (inflatedPosition S D.tree β.toNode).1 := rfl
  rw [e1]
  by_cases h1 : (chainContextNode D hS β a).1.2 ≠ []
  · by_cases h2 : (layeredReconstruction D hS layer hLayer).layer (chainContextNode D hS β a) < p ∧
        (layeredReconstruction D hS layer hLayer).parentLayer p (chainContextNode D hS β a) = p
    · simp only [h1, h2, and_self, ↓reduceIte, ne_eq, not_false_eq_true]
    · simp only [h1, h2, ↓reduceIte, ne_eq, not_false_eq_true, and_false]
  · simp only [h1, ↓reduceIte, false_and]

theorem pc_norm_starWeight_le (p : ℕ) (Rf : Fin w → Option ℝ)
    (K : GNode (nativeChainLayered D hS layer hLayer β).garden.tree → Mom d) :
    ‖IncTop.starWeight (pc_frontS D hS layer hLayer β p) (pc_ω D hS layer hLayer β Rf) K‖ ≤ 1 := by
  unfold IncTop.starWeight
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun a _ => ?_
  unfold pc_ω IncTop.topStar frontierG
  rw [Complex.norm_real, Real.norm_eq_abs]
  cases Rf (inflatedPosition S D.tree β.toNode).1 with
  | none => simp
  | some r =>
    simp only [Option.elim]
    rw [abs_of_nonneg (XChain.ProductCut.chi0_nonneg _)]
    exact XChain.ProductCut.chi0_le_one _

theorem pc_frontS_card_le (p : ℕ) :
    (pc_frontS D hS layer hLayer β p).card ≤ Stage1WNoVine.slotNr D hS (.inr β) := by
  unfold Stage1WNoVine.slotNr
  refine Finset.card_le_card fun a ha => ?_
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 ha).2.1⟩

end Slot

/-! ## The stem node weight at a branch -/

section NW

variable (LG : LayeredGarden w) (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)

/-- The radius of σ's filter in a tree. -/
def pcRad (j : Fin w) : ℝ := (σ j).elim L fun i => 2 ^ i * L

theorem radProd_append (r₁ r₂ : List ℝ) (x : ℝ) :
    MkSlotsT.radProd (r₁ ++ r₂) x = MkSlotsT.radProd r₁ x * MkSlotsT.radProd r₂ x := by
  unfold MkSlotsT.radProd
  rw [List.map_append, List.prod_append]

theorem pc_radProd_radSigma (B : GBranch LG.garden.tree) (x : ℝ) :
    MkSlotsT.radProd (MkSlotsT.radSigma L σ B) x =
      if (σ B.1.1).isSome then chi0 (|x| / pcRad L σ B.1.1) else 1 := by
  unfold MkSlotsT.radSigma MkSlotsT.radProd pcRad
  cases σ B.1.1 <;> simp

theorem pc_radProd_shellRad (B : GBranch LG.garden.tree) (x : ℝ) :
    MkSlotsT.radProd (MkSlotsG.shellRad LG J kSel Rs B) x =
      if MkSlotsG.shellRad LG J kSel Rs B ≠ [] then chi0 (|x| / Rs B.1.1) else 1 := by
  unfold MkSlotsG.shellRad MkSlotsT.radProd
  split_ifs <;> simp_all

/-- The stem node weight at a branch, unfolded (copied from HELPER7's `MkSlotsI.genNW_br`). -/
theorem pc_genNW_br0 (B : GBranch LG.garden.tree) (x : ℝ) :
    MkSlotsI.genNW LG J L σ kSel Rs B.toNode x =
      if ∃ j, B ∈ stemSetCap LG J j then
        (MkSlotsT.radProd (MkSlotsG.radRaw LG J L σ kSel Rs B) x : ℂ) *
          (if B ∈ selSetCap LG J kSel then ((chiD (|x| / Rs B.1.1) : ℝ) : ℂ) else 1)
      else 1 := by
  have hb : (B.toNode).1.2 ∈ (LG.garden.tree (B.toNode).1.1).branching := B.2
  have he : (⟨(B.toNode).1, hb⟩ : GBranch LG.garden.tree) = B := rfl
  unfold MkSlotsI.genNW
  rw [dite_eq_left hb, he]
  split_ifs <;> first | rfl | contradiction

/-- The stem node weight at a branch, as three filters. -/
theorem pc_genNW_br (B : GBranch LG.garden.tree) (x : ℝ) :
    MkSlotsI.genNW LG J L σ kSel Rs B.toNode x =
      (if (∃ j, B ∈ stemSetCap LG J j) ∧ (σ B.1.1).isSome then ((chi0 (|x| / pcRad L σ B.1.1) : ℝ) : ℂ) else 1) *
        (if (∃ j, B ∈ stemSetCap LG J j) ∧ MkSlotsG.shellRad LG J kSel Rs B ≠ [] then
          ((chi0 (|x| / Rs B.1.1) : ℝ) : ℂ) else 1) *
        (if (∃ j, B ∈ stemSetCap LG J j) ∧ B ∈ selSetCap LG J kSel then ((chiD (|x| / Rs B.1.1) : ℝ) : ℂ)
          else 1) := by
  rw [pc_genNW_br0]
  by_cases hst : ∃ j, B ∈ stemSetCap LG J j
  · simp only [hst, true_and, ↓reduceIte, MkSlotsG.radRaw, radProd_append, pc_radProd_radSigma,
      pc_radProd_shellRad]
    split_ifs <;> push_cast <;> ring
  · simp only [hst, false_and, ↓reduceIte, mul_one]

theorem pc_genNW_not_branch (z : GNode LG.garden.tree) (hz : z.1.2 ∉ (LG.garden.tree z.1.1).branching) (x : ℝ) :
    MkSlotsI.genNW LG J L σ kSel Rs z x = 1 := by
  unfold MkSlotsI.genNW
  rw [dite_eq_right hz]

end NW

/-- A product over the nodes of a function that is `1` off the branches is a product over the branches. -/
theorem pc_prod_nodes {T : Fin w → TTree} (f : GNode T → ℂ)
    (hf : ∀ a : GNode T, a.1.2 ∉ (T a.1.1).branching → f a = 1) :
    ∏ a, f a = ∏ b : GBranch T, f b.toNode := by
  have hinj : Function.Injective (fun b : GBranch T => b.toNode) := by
    intro b b' h
    have h2 : (b.toNode).1 = (b'.toNode).1 := congrArg Subtype.val h
    exact Subtype.ext h2
  rw [← Finset.prod_image (s := Finset.univ) (f := f) (fun x _ y _ h => hinj h)]
  refine (Finset.prod_subset (Finset.subset_univ _) fun a _ ha => hf a fun hb => ha ?_).symm
  exact Finset.mem_image.2 ⟨⟨a.1, hb⟩, Finset.mem_univ _, rfl⟩

/-- A two-valued filter weight is bounded by `chiDNorm ^ #F`. -/
theorem pc_norm_filtWeight_le {G : Garden w} (F : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool)
    (M : GBranch G.tree → ℝ) (k : GNode G.tree → Mom d) : ‖filtWeight F ann M k‖ ≤ chiDNorm ^ F.card := by
  unfold filtWeight
  rw [norm_prod, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun b _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  cases ann b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [abs_of_nonneg (XChain.ProductCut.chi0_nonneg _)]
    exact (XChain.ProductCut.chi0_le_one _).trans one_le_chiDNorm
  · simp only [↓reduceIte]
    exact abs_chiD_le_chiDNorm _

section Theta

variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) (β : GBranch S.tree)
  (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)

/-- A branch of the native chain as a branch of the reconstruction. -/
abbrev pcB (b : GBranch (nativeChainLayered D hS layer hLayer β).garden.tree) :
    GBranch (layeredReconstruction D hS layer hLayer).garden.tree :=
  MkSlotsB.nativeBr D hS (.inr β) b

/-- The tree of the chain. -/
abbrev pcj : Fin w := (inflatedPosition S D.tree β.toNode).1

/-- The per-slot factor of a chain slot as a function of the momenta of its native chain. -/
def pcΘ (K : GNode (nativeChainLayered D hS layer hLayer β).garden.tree → Mom d) : ℂ :=
  ∏ a : GNode (decodedTree (D.tree β) (nodeSign S.sig β.1)).tree,
    if ∃ β' : GBranch S.tree, chainContextNode D hS β a = (D.coreBranch hS β').toNode then 1
    else MkSlotsI.genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs (chainContextNode D hS β a)
      (MkSlotsS.omegaAt K a)

/-- A branch of the native chain is on the capped stem. -/
def PcSt (b : GBranch (nativeChainLayered D hS layer hLayer β).garden.tree) : Prop :=
  ∃ j, pcB D hS layer hLayer β b ∈ stemSetCap (layeredReconstruction D hS layer hLayer) J j

/-- The σ-filtered branches. -/
def pcFσ : Finset (GBranch (nativeChainLayered D hS layer hLayer β).garden.tree) :=
  Finset.univ.filter fun b => PcSt D hS layer hLayer β J b ∧ (σ (pcj D β)).isSome

/-- The shell-filtered branches. -/
def pcFsh : Finset (GBranch (nativeChainLayered D hS layer hLayer β).garden.tree) :=
  Finset.univ.filter fun b => PcSt D hS layer hLayer β J b ∧
    MkSlotsG.shellRad (layeredReconstruction D hS layer hLayer) J kSel Rs (pcB D hS layer hLayer β b) ≠ []

/-- The selected branches. -/
def pcFsel : Finset (GBranch (nativeChainLayered D hS layer hLayer β).garden.tree) :=
  Finset.univ.filter fun b => PcSt D hS layer hLayer β J b ∧
    pcB D hS layer hLayer β b ∈ selSetCap (layeredReconstruction D hS layer hLayer) J kSel

/-- **The per-slot factor of a chain slot**: σ filters, selection shells and selected filters over the branches
of the native chain. -/
theorem pcΘ_eq (K : GNode (nativeChainLayered D hS layer hLayer β).garden.tree → Mom d) :
    pcΘ D hS layer hLayer β J L σ kSel Rs K =
      filtWeight (pcFσ D hS layer hLayer β J σ) (fun _ => false) (fun _ => pcRad L σ (pcj D β)) K *
        filtWeight (pcFsh D hS layer hLayer β J kSel Rs) (fun _ => false) (fun _ => Rs (pcj D β)) K *
        ∏ b ∈ pcFsel D hS layer hLayer β J kSel,
          ((chiD (|omegaNode (nativeChainLayered D hS layer hLayer β).garden K b| / Rs (pcj D β)) : ℝ) : ℂ) := by
  unfold pcΘ
  rw [pc_prod_nodes (T := (decodedTree (D.tree β) (nodeSign S.sig β.1)).tree)]
  · unfold filtWeight pcFσ pcFsh pcFsel
    rw [Finset.prod_filter, Finset.prod_filter, Finset.prod_filter, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b _ => ?_
    have hnc : ¬ ∃ β' : GBranch S.tree, chainContextNode D hS β b.toNode = (D.coreBranch hS β').toNode :=
      fun h => pc_lone_not_branch D hS layer hLayer β b ((pc_chain_core_iff D hS layer hLayer β b.toNode).mp h)
    have e1 : chainContextNode D hS β b.toNode = (pcB D hS layer hLayer β b).toNode := Subtype.ext rfl
    have e2 : MkSlotsS.omegaAt K b.toNode = omegaNode (nativeChainLayered D hS layer hLayer β).garden K b := by
      unfold MkSlotsS.omegaAt
      exact dite_eq_left b.2
    simp only [hnc, ↓reduceIte]
    rw [e1, e2, pc_genNW_br]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (if_congr Iff.rfl rfl rfl) (if_congr Iff.rfl rfl rfl))
      (if_congr Iff.rfl rfl rfl)
  · intro a ha
    by_cases hc : ∃ β' : GBranch S.tree, chainContextNode D hS β a = (D.coreBranch hS β').toNode
    · simp only [hc, ↓reduceIte]
    · simp only [hc, ↓reduceIte]
      exact pc_genNW_not_branch _ _ _ _ _ _ _
        (fun h => ha (pc_chain_branch_of_branch' D hS β a h fun he => hc ⟨β, he⟩)) _

end Theta

end WaveTurbulence.Flower.MkSlotsO
