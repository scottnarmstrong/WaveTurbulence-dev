/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.PcD3

/-! # PROT-CHAIN (`Pc`): an absorbed selected vertex on a stem chain, from D6 (`none`, `Sel = {v}`)

A stem chain slot `.inr β` with no pinned native branch (`objCfg = none`) and a selected vertex `v` as a non-core native
node (δ's `selVertex_dichotomy` (b)): the per-slot factor is `chiD(|Ω_v|/Rs_j)` at `v`, σ's filter at every stem branch
and the shells `χ₀(|Ω|/Rs_j)` at the stem branches other than `v`. In D6's form: the first layer is σ's filters off
`v` plus the selected annular filter at `v` (`M₂ = Rs_j`), the second layer the shells plus σ's filter at `v`. D6's
`ProtAnnBoundAt` (`pin = false`, `Sel = {v}`, R183's lone-node layer) gives `L^{47d+5} · Rs_j^{-1/18}`, matched by the
slot mass (`selNative = {v}`).

* `pc_split6`: the filter regrouping;
* `pc_selBranch`: the selected native branch; `pc_Fsel_single`, `pc_not_Fsh`, `pc_selNative_single`;
* **`pc_d6_fam`**: the slot family at `θ = η`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open Set
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlotsI
  WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.Stage1WNoVine

namespace WaveTurbulence.Flower.MkSlotsO

/-- **The filter regrouping** for D6: `σ` off `v` and `chiD` at `v` in the first layer, the shells and `σ` at `v` in the
second. -/
theorem pc_split6 {w d : ℕ} {G : Garden w} (K : GNode G.tree → Mom d) (F Fu : Finset (GBranch G.tree))
    (bv : GBranch G.tree) (hbv : bv ∉ Fu) (M₁ M₂ : ℝ) :
    filtWeight F (fun _ => false) (fun _ => M₁) K * filtWeight Fu (fun _ => false) (fun _ => M₂) K *
        ∏ b ∈ ({bv} : Finset (GBranch G.tree)), ((chiD (|omegaNode G K b| / M₂) : ℝ) : ℂ) =
      filtWeight (F.filter (· ≠ bv) ∪ {bv}) (fun b => decide (b ∈ ({bv} : Finset (GBranch G.tree))))
          (fun b => if b ∈ ({bv} : Finset (GBranch G.tree)) then M₂ else M₁) K *
        filtWeight (Fu ∪ F.filter (· = bv)) (fun _ => false) (fun b => if b = bv then M₁ else M₂) K := by
  have hd1 : Disjoint (F.filter (· ≠ bv)) {bv} :=
    Finset.disjoint_singleton_right.2 fun h => (Finset.mem_filter.1 h).2 rfl
  have hd2 : Disjoint Fu (F.filter (· = bv)) :=
    Finset.disjoint_left.2 fun b hb hb' => hbv ((Finset.mem_filter.1 hb').2 ▸ hb)
  have hR1 : filtWeight (F.filter (· ≠ bv) ∪ {bv}) (fun b => decide (b ∈ ({bv} : Finset (GBranch G.tree))))
      (fun b => if b ∈ ({bv} : Finset (GBranch G.tree)) then M₂ else M₁) K =
      (∏ b ∈ F.filter (· ≠ bv), ((chi0 (|omegaNode G K b| / M₁) : ℝ) : ℂ)) *
        ((chiD (|omegaNode G K bv| / M₂) : ℝ) : ℂ) := by
    unfold filtWeight
    rw [Finset.prod_union hd1, Finset.prod_singleton]
    congr 1
    · refine Finset.prod_congr rfl fun b hb => ?_
      have hb' : b ≠ bv := (Finset.mem_filter.1 hb).2
      simp [hb']
    · simp only [Finset.mem_singleton, decide_true, ↓reduceIte]
      rfl
  have hR2 : filtWeight (Fu ∪ F.filter (· = bv)) (fun _ => false) (fun b => if b = bv then M₁ else M₂) K =
      (∏ b ∈ Fu, ((chi0 (|omegaNode G K b| / M₂) : ℝ) : ℂ)) *
        ∏ b ∈ F.filter (· = bv), ((chi0 (|omegaNode G K b| / M₁) : ℝ) : ℂ) := by
    unfold filtWeight
    rw [Finset.prod_union hd2]
    congr 1
    · refine Finset.prod_congr rfl fun b hb => ?_
      have hb' : b ≠ bv := fun h => hbv (h ▸ hb)
      simp [hb']
    · refine Finset.prod_congr rfl fun b hb => ?_
      have hb' : b = bv := (Finset.mem_filter.1 hb).2
      simp [hb']
  have hL1 : filtWeight F (fun _ => false) (fun _ => M₁) K =
      (∏ b ∈ F.filter (· ≠ bv), ((chi0 (|omegaNode G K b| / M₁) : ℝ) : ℂ)) *
        ∏ b ∈ F.filter (· = bv), ((chi0 (|omegaNode G K b| / M₁) : ℝ) : ℂ) := by
    unfold filtWeight
    rw [← Finset.prod_filter_mul_prod_filter_not F (· ≠ bv)]
    have hf : F.filter (fun b => ¬ b ≠ bv) = F.filter (· = bv) := by
      congr 1
      funext b
      simp
    rw [hf]
    simp
  have hL2 : filtWeight Fu (fun _ => false) (fun _ => M₂) K =
      ∏ b ∈ Fu, ((chi0 (|omegaNode G K b| / M₂) : ℝ) : ℂ) := by
    unfold filtWeight
    simp
  rw [hR1, hR2, hL1, hL2, Finset.prod_singleton]
  ring

section Sel

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) (β : GBranch S.tree) (J : Finset (Fin w)) (kSel : Fin w → Option ℕ)

/-- The selected native branch. -/
theorem pc_selBranch (y : GNode (decodedTree (D.tree β) (nodeSign S.sig β.1)).tree)
    (hy : ∀ β' : GBranch S.tree, chainContextNode D hS β y ≠ (D.coreBranch hS β').toNode)
    (v : GBranch (layeredReconstruction D hS layer hLayer).garden.tree)
    (hvy : v.1 = (chainContextNode D hS β y).1) :
    ∃ bv : GBranch (nativeChainLayered D hS layer hLayer β).garden.tree, pcB D hS layer hLayer β bv = v := by
  have hbr : (chainContextNode D hS β y).1.2 ∈ ((D.forest hS) (chainContextNode D hS β y).1.1).branching := by
    rw [← hvy]; exact v.2
  refine ⟨⟨y.1, pc_chain_branch_of_branch' D hS β y hbr (hy β)⟩, Subtype.ext ?_⟩
  exact hvy.symm

theorem pcB_inj {b b' : GBranch (nativeChainLayered D hS layer hLayer β).garden.tree}
    (h : pcB D hS layer hLayer β b = pcB D hS layer hLayer β b') : b = b' := by
  have h1 : (pcu D β).2 ++ b.1.2 = (pcu D β).2 ++ b'.1.2 := congrArg (fun z => z.1.2) h
  exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) (List.append_cancel_left h1))

variable {v : GBranch (layeredReconstruction D hS layer hLayer).garden.tree}
  (hv : v ∈ selSetCap (layeredReconstruction D hS layer hLayer) J kSel)
  {bv : GBranch (nativeChainLayered D hS layer hLayer β).garden.tree} (hbv : pcB D hS layer hLayer β bv = v)
include hv hbv

theorem pc_selCap_v : selCap (layeredReconstruction D hS layer hLayer) J kSel (pcj D β) = some v := by
  have h := MkSlotsS.selCap_of_mem_selSetCap hv
  rw [← hbv] at h ⊢
  exact h

theorem pc_Fsel_single : pcFsel D hS layer hLayer β J kSel = {bv} := by
  have hs := pc_selCap_v D hS layer hLayer β J kSel hv hbv
  ext b
  simp only [pcFsel, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hb⟩
    have h := MkSlotsS.selCap_of_mem_selSetCap hb
    have e : selCap (layeredReconstruction D hS layer hLayer) J kSel (pcj D β) = some (pcB D hS layer hLayer β b) := h
    rw [hs] at e
    exact pcB_inj D hS layer hLayer β ((Option.some.inj e).symm.trans hbv.symm)
  · rintro rfl
    refine ⟨⟨pcj D β, ?_⟩, hbv ▸ hv⟩
    rw [hbv]
    exact (MkSlotsS.selCap_spec hs).2

theorem pc_not_Fsh (Rs : Fin w → ℝ) : bv ∉ pcFsh D hS layer hLayer β J kSel Rs := by
  have hs := pc_selCap_v D hS layer hLayer β J kSel hv hbv
  simp only [pcFsh, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
  intro _ h
  apply h
  unfold MkSlotsG.shellRad
  rw [ite_eq_right_iff]
  rintro ⟨v', hv', hne⟩
  have e : selCap (layeredReconstruction D hS layer hLayer) J kSel (pcj D β) = some v' := hv'
  rw [hs] at e
  exact absurd (hbv.trans (Option.some.inj e)) (Ne.symm hne)

theorem pc_selNative_single (y : GNode (decodedTree (D.tree β) (nodeSign S.sig β.1)).tree)
    (hy : ∀ β' : GBranch S.tree, chainContextNode D hS β y ≠ (D.coreBranch hS β').toNode)
    (hvy : v.1 = (chainContextNode D hS β y).1) :
    MkSlotsS.selNative D hS layer hLayer J kSel (.inr β) = {v} := by
  have hs := pc_selCap_v D hS layer hLayer β J kSel hv hbv
  ext v'
  simp only [MkSlotsS.selNative, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hv', y', -, hy'⟩
    have h1 : v'.1.1 = pcj D β := by
      have h := congrArg Prod.fst hy'
      exact h
    have h2 := MkSlotsS.selCap_of_mem_selSetCap hv'
    rw [h1, hs] at h2
    exact (Option.some.inj h2).symm
  · rintro rfl
    exact ⟨hv, y, hy, hvy⟩

end Sel

end WaveTurbulence.Flower.MkSlotsO
