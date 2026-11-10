/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepSlots2
public import WaveTurbulence.Foundations.Stage1.Represents.RepSlotNum3M
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-D (moments): the per-slot superpositions with the frequency moment

`SlotRepM θ`: per-slot superpositions (`CenSupM θ` at pairs, `SupM θ` at branches) whose weights carry `⟨m/2⟩^θ`.
`slots_existM`: the moment-carrying form of `slots_exist` (RepSlots2), at `θ = η`, with the same per-slot masses up to
the constant `KslotM`.  `SlotRepM.toSlotRep` forgets the moment.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RegRed
  WaveTurbulence.RepAnalytic WaveTurbulence.PL2330 WaveTurbulence.RegRedLeaf
open scoped ENNReal

/-- Per-slot superpositions with the frequency moment `θ`. -/
structure SlotRepM {w : ℕ} (θ : ℝ) (S : Garden w) (hS : S.IsPlain) (d : ℕ) (layer0 : GBranch S.tree → ℕ)
    (tt : Fin w → ℝ) where
  Fn : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ
  Box : ReplacementSlot S → Set (Fin 2 → ℝ)
  μ : ReplacementSlot S → ℝ≥0∞
  cp : ∀ p, CenSupM θ (30 * d) (Box (Sum.inl p)) (Fn (Sum.inl p)) (μ (Sum.inl p))
  tr : ∀ b, SupM θ (30 * d) (Box (Sum.inr b)) (Fn (Sum.inr b)) (μ (Sum.inr b))
  hbox : ∀ τ ∈ splicedTimeDomain S layer0 tt, ∀ s, slotTs hS tt τ s ∈ Box s

open scoped Classical in
/-- The explicit moment-carrying slot constant (depends only on `d` and `η`). -/
noncomputable def KslotM (d : ℕ) (η : ℝ) : ℝ := max (KcplM d η) (KtrM d η)

theorem slots_existM (Pg : WTParams) (E : GateEnv Pg) :
    ∃ K : ℝ, 1 ≤ K ∧ K = KslotM Pg.d Pg.η ∧ ∀ (C : ℝ), 2 * Pg.C₁ ^ 2 * (1 + cLeib Pg.d (30 * Pg.d)) ≤ C →
      ∀ {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
        (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (p : ℕ),
        p < Pg.D → D.size ≤ Pg.N (p + 1) ^ 4 →
        IsCanonGC (p + 1) (layeredReconstruction D hS layer hLayer) →
        ∀ (tt : Fin w → ℝ), (∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) →
        ∀ (H : LeafProfiles w Pg.d) (B : (Fin w × TTree.Path) → NNReal),
        LeafwiseControlled (layeredReconstruction D hS layer hLayer) H B →
        ∃ Rep : SlotRepM Pg.η S hS Pg.d (fun b => layer (D.coreBranch hS b).toNode) tt,
          Rep.Box = slotBox p (fun b => layer (D.coreBranch hS b).toNode) hS ∧
          Rep.Fn = slotFn D hS Pg.L Pg.γ Pg.δ H layer hLayer ∧
          ∀ s, Rep.μ s ≤ ENNReal.ofReal (K * (C * Real.sqrt Pg.δ) ^ (slotSize D s) *
            Pg.L ^ (-(Pg.η ^ 8) * (slotIncoh D hS layer hLayer s : ℝ)) * slotLeaf D hS layer hLayer B s) := by
  obtain ⟨Kc, hKc1, hKce, hc⟩ := couple_slot_targetM Pg E
  obtain ⟨Kt, hKt1, hKte, ht⟩ := tree_slot_targetM Pg E
  refine ⟨max Kc Kt, le_trans hKc1 (le_max_left _ _), by rw [KslotM, hKce, hKte], fun C hC w S D hS layer hLayer p hp hN hcan tt htt H B hctrl => ?_⟩
  have hL0 : 0 < Pg.L := lt_of_lt_of_le zero_lt_one E.hL1
  have hlay : ∀ ν, layer ν ≤ p := fun ν => WaveTurbulence.Canon.layer_le_of_isCanonGC hcan ν
  have hC0 : 0 ≤ C := by nlinarith [E.hC1, cLeib_nonneg Pg.d (30 * Pg.d)]
  have hx : ∀ k : ℕ, 0 ≤ (C * Real.sqrt Pg.δ) ^ k := fun k => pow_nonneg (mul_nonneg hC0 (Real.sqrt_nonneg _)) k
  have hLp : ∀ g : ℝ, 0 ≤ Pg.L ^ (-(Pg.η ^ 8) * g) := fun g => Real.rpow_nonneg hL0.le _
  have hlf : ∀ s, 0 ≤ slotLeaf D hS layer hLayer B s := by
    intro s
    cases s with
    | inl p' => exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    | inr b => exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  refine ⟨{ Fn := slotFn D hS Pg.L Pg.γ Pg.δ H layer hLayer
            Box := slotBox p (fun b => layer (D.coreBranch hS b).toNode) hS
            μ := fun s => ENNReal.ofReal (max Kc Kt * (C * Real.sqrt Pg.δ) ^ (slotSize D s) *
              Pg.L ^ (-(Pg.η ^ 8) * (slotIncoh D hS layer hLayer s : ℝ)) * slotLeaf D hS layer hLayer B s)
            cp := ?_, tr := ?_, hbox := ?_ }, rfl, rfl, fun s => le_rfl⟩
  · intro p'
    obtain ⟨m, hm⟩ := code_size_even (D.couple p')
    have hn2 : (D.couple p').size = 2 * m := by omega
    have hsl := slotSize_le D (.inl p')
    have hn : m ≤ Pg.N (p + 1) ^ 4 := by
      have : slotSize D (.inl p') = (D.couple p').size := rfl
      omega
    have hq0 := clkLayer_le D hS layer p hlay (argSrc hS (.inl p') 0)
    have hq1 := clkLayer_le D hS layer p hlay (argSrc hS (.inl p') 1)
    have hcase : D.couple p' = RegCpl.triv ∨ (1 ≤ m ∧ (1 ≤ (nativeCoupleLayered D hS layer hLayer p').incoherency
        (D.couple p').links ∨ ((nativeCoupleLayered D hS layer hLayer p').incoherency (D.couple p').links = 0 ∧
        IsCoherentCoupleAt p
          (clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS (.inl p') 0))
          (clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS (.inl p') 1))
          (D.couple p') (nativeCoupleLayered D hS layer hLayer p')))) := by
      by_cases htriv : D.couple p' = RegCpl.triv
      · exact Or.inl htriv
      · refine Or.inr ⟨?_, ?_⟩
        · have := cpl_two_le _ (D.couple_wf p') htriv
          omega
        · by_cases hg : (nativeCoupleLayered D hS layer hLayer p').incoherency (D.couple p').links = 0
          · exact Or.inr ⟨hg, couple_coherent_at D hS layer hLayer p hcan p' hg⟩
          · exact Or.inl (Nat.one_le_iff_ne_zero.2 hg)
    have h := hc C hC p m hp hn (D.couple p') (D.couple_wf p') hn2 (nativeCoupleLayered D hS layer hLayer p')
      (couple_decodes D hS layer hLayer p') (fun a => hlay _) _ _ hq0 hq1
      (couple_root_layer_le D hS layer hLayer p hlay p' 0) (couple_root_layer_le D hS layer hLayer p hlay p' 1)
      hcase (nativeCoupleProfiles D hS H p') (nativeCoupleB D hS B p')
      (couple_controlled D hS layer hLayer H B hctrl p')
    exact h.mono (mass_mono _ _ _ _ _ (le_max_left _ _) (hx _) (hLp _) (hlf (.inl p')))
  · intro b
    obtain ⟨m, hm⟩ := chain_size_even (D.tree b)
    have hn2 : (D.tree b).size = 2 * m := by omega
    have hsl := slotSize_le D (.inr b)
    have hn : m ≤ Pg.N (p + 1) ^ 4 := by
      have : slotSize D (.inr b) = (D.tree b).size := rfl
      omega
    have hq0 := clkLayer_le D hS layer p hlay (argSrc hS (.inr b) 0)
    have hq1 := clkLayer_le D hS layer p hlay (argSrc hS (.inr b) 1)
    have hcase : D.tree b = RegChain.nil ∨ (1 ≤ m ∧ (1 ≤ (nativeChainLayered D hS layer hLayer b).incoherency
        ((D.tree b).treeLinks ((nativeChainLayered D hS layer hLayer b).garden.sig 0)) ∨
        ((nativeChainLayered D hS layer hLayer b).incoherency
          ((D.tree b).treeLinks ((nativeChainLayered D hS layer hLayer b).garden.sig 0)) = 0 ∧
        IsCoherentTreeAt p
          (clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS (.inr b) 0))
          (clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS (.inr b) 1))
          (D.tree b) (nativeChainLayered D hS layer hLayer b)))) := by
      by_cases hnil : D.tree b = RegChain.nil
      · exact Or.inl hnil
      · refine Or.inr ⟨?_, ?_⟩
        · have := chain_two_le _ hnil
          omega
        · by_cases hg : (nativeChainLayered D hS layer hLayer b).incoherency
              ((D.tree b).treeLinks ((nativeChainLayered D hS layer hLayer b).garden.sig 0)) = 0
          · exact Or.inr ⟨hg, tree_coherent_at D hS layer hLayer p hcan b hg⟩
          · exact Or.inl (Nat.one_le_iff_ne_zero.2 hg)
    have h := ht C hC p m hp hn (D.tree b) (D.tree_wf b) hn2 (nativeChainLayered D hS layer hLayer b)
      (tree_decodes D hS layer hLayer b) (tree_noFlower D hS layer hLayer b) (fun j => tree_lone_card D hS layer hLayer b j)
      (fun a => hlay _) _ _ (tree_q'_le_q D hS layer hLayer p hlay b) hq0
      (tree_root_layer_le D hS layer hLayer p hlay b)
      (fun a ha => tree_lone_layer D hS layer hLayer b a ha) hcase (nativeChainProfiles D hS H b)
      (nativeChainB D hS B b) (chain_controlled D hS layer hLayer H B hctrl b)
    exact h.mono (mass_mono _ _ _ _ _ (le_max_right _ _) (hx _) (hLp _) (hlf (.inr b)))
  · intro τ hτ s
    exact slotTs_mem_slotBox p (fun b => layer (D.coreBranch hS b).toNode) hS tt htt τ hτ s

end WaveTurbulence.Represents
