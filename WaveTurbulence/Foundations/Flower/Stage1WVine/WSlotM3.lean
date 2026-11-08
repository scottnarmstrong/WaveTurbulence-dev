/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.WSlotM2
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.Core2
public import WaveTurbulence.Foundations.Stage1.Represents.RepSlots2M

/-! # STAGE1W-VINE (O3b): moment-carrying superpositions of the frontier-weighted outer slot kernels

`slots_existMW`: STAGE1W-O4's `slots_existW` (copied by source, sha256 in `COPIED-SHA256SUMS`) in main's
moment-carrying `SlotRepM P.η` form (`slots_existM`, RepSlots2M), with the slot boxes `slotBox` recorded.  Per slot the
mass is O4′'s: main's slot mass times `cψ ^ slotNr` (the garden-nonroot nodes of the slot), constant `KslotMW d η`.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
namespace WaveTurbulence.Flower.Stage1WVine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Represents WaveTurbulence.VineEstS3.FS MeasureTheory Set
  WaveTurbulence.Flower.Stage1W WaveTurbulence.Reg WaveTurbulence.PL2330 WaveTurbulence.Flower.Stage1WNoVine
  TTree Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.RepAnalytic WaveTurbulence.RegRedLeaf

noncomputable def KslotMW (d : ℕ) (η : ℝ) : ℝ := max (KcplMW d η) (KtrMW d η)

/-- **Moment-carrying per-slot superpositions of the weighted slot kernels** (main's `slots_existM`, weighted). -/
theorem slots_existMW (Pg : WTParams) (E : GateEnv Pg) (hinc : TopIncoherentDecayAtR Pg) :
    ∃ K : ℝ, 1 ≤ K ∧ K = KslotMW Pg.d Pg.η ∧ ∀ (C : ℝ), 2 * Pg.C₁ ^ 2 * (1 + cLeib Pg.d (30 * Pg.d)) ≤ C →
      ∀ {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
        (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (p : ℕ),
        p < Pg.D → D.size ≤ Pg.N (p + 1) ^ 4 →
        IsCanonGC (p + 1) (layeredReconstruction D hS layer hLayer) →
        ∀ (tt : Fin w → ℝ), (∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) →
        ∀ (H : LeafProfiles w Pg.d) (B : (Fin w × TTree.Path) → NNReal),
        LeafwiseControlled (layeredReconstruction D hS layer hLayer) H B →
        ∀ (g : Fin w → Mom Pg.d → ℂ) (cψ : ℝ), 1 ≤ cψ → (∀ j, GPresented (32 * Pg.d) (g j) cψ) →
        ∃ Rep : SlotRepM Pg.η S hS Pg.d (fun b => layer (D.coreBranch hS b).toNode) tt,
          Rep.Box = slotBox p (fun b => layer (D.coreBranch hS b).toNode) hS ∧ Rep.Fn = slotFnNW D hS Pg.L Pg.γ Pg.δ H (fwNode (layeredReconstruction D hS layer hLayer) p g)
            layer hLayer ∧
          ∀ s, Rep.μ s ≤ ENNReal.ofReal (K * cψ ^ slotNr D hS s * (C * Real.sqrt Pg.δ) ^ (slotSize D s) *
            Pg.L ^ (-(Pg.η ^ 8) * (slotIncoh D hS layer hLayer s : ℝ)) * slotLeaf D hS layer hLayer B s) := by
  obtain ⟨Kc, hKc1, hKce, hc⟩ := couple_slot_targetMW Pg E hinc
  obtain ⟨Kt, hKt1, hKte, ht⟩ := tree_slot_targetMW Pg E hinc
  refine ⟨max Kc Kt, le_trans hKc1 (le_max_left _ _), by rw [KslotMW, hKce, hKte], fun C hC w S D hS layer hLayer p hp hN hcan tt htt H B hctrl
    g cψ hc1 hg => ?_⟩
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
  have hmono : ∀ (K0 : ℝ) (e e' : ℕ) (s : ReplacementSlot S), K0 ≤ max Kc Kt → e ≤ e' →
      ENNReal.ofReal (K0 * cψ ^ e * (C * Real.sqrt Pg.δ) ^ (slotSize D s) *
        Pg.L ^ (-(Pg.η ^ 8) * (slotIncoh D hS layer hLayer s : ℝ)) * slotLeaf D hS layer hLayer B s) ≤
      ENNReal.ofReal (max Kc Kt * cψ ^ e' * (C * Real.sqrt Pg.δ) ^ (slotSize D s) *
        Pg.L ^ (-(Pg.η ^ 8) * (slotIncoh D hS layer hLayer s : ℝ)) * slotLeaf D hS layer hLayer B s) := by
    intro K0 e e' s hK0 hee
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : cψ ^ e ≤ cψ ^ e' := pow_le_pow_right₀ hc1 hee
    have h2 := hx (slotSize D s)
    have h3 := hLp (slotIncoh D hS layer hLayer s : ℝ)
    have h4 := hlf s
    have h5 : 0 ≤ cψ ^ e := by positivity
    by_cases hK00 : 0 ≤ K0
    · gcongr
    · have : K0 * cψ ^ e * (C * Real.sqrt Pg.δ) ^ (slotSize D s) *
          Pg.L ^ (-(Pg.η ^ 8) * (slotIncoh D hS layer hLayer s : ℝ)) * slotLeaf D hS layer hLayer B s ≤ 0 := by
        have : K0 * cψ ^ e ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) h5
        have : 0 ≤ (C * Real.sqrt Pg.δ) ^ (slotSize D s) * Pg.L ^ (-(Pg.η ^ 8) * (slotIncoh D hS layer hLayer s : ℝ)) *
            slotLeaf D hS layer hLayer B s := by positivity
        nlinarith
      refine this.trans ?_
      have : 0 ≤ max Kc Kt := by linarith [le_max_left Kc Kt]
      positivity
  refine ⟨{ Fn := slotFnNW D hS Pg.L Pg.γ Pg.δ H (fwNode (layeredReconstruction D hS layer hLayer) p g) layer hLayer
            Box := slotBox p (fun b => layer (D.coreBranch hS b).toNode) hS
            μ := fun s => ENNReal.ofReal (max Kc Kt * cψ ^ slotNr D hS s * (C * Real.sqrt Pg.δ) ^ (slotSize D s) *
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
        · by_cases hg0 : (nativeCoupleLayered D hS layer hLayer p').incoherency (D.couple p').links = 0
          · exact Or.inr ⟨hg0, couple_coherent_at D hS layer hLayer p hcan p' hg0⟩
          · exact Or.inl (Nat.one_le_iff_ne_zero.2 hg0)
    have h := hc C hC p m hp hn (D.couple p') (D.couple_wf p') hn2 (nativeCoupleLayered D hS layer hLayer p')
      (couple_decodes D hS layer hLayer p') (fun a => hlay _) _ _ hq0 hq1
      (couple_root_layer_le D hS layer hLayer p hlay p' 0) (couple_root_layer_le D hS layer hLayer p hlay p' 1)
      hcase (nativeCoupleProfiles D hS H p') (nativeCoupleB D hS B p')
      (couple_controlled D hS layer hLayer H B hctrl p') (cplG D hS g p') cψ hc1 (fun j => hg _)
      (cplQ D hS layer hLayer p p' 0) (cplQ D hS layer hLayer p p' 1)
      (cplQ_spec D hS layer hLayer p p' 0) (cplQ_spec D hS layer hLayer p p' 1)
    refine (CenSupM.congr' h fun ts _ k => (slotFnNW_fw_couple D hS layer hLayer Pg.L Pg.γ Pg.δ H p g p' ts k).symm).mono ?_
    exact hmono Kc _ _ (.inl p') (le_max_left _ _) (cplExp_le_slotNr D hS layer hLayer p p')
  · intro b
    obtain ⟨m, hm⟩ := chain_size_even (D.tree b)
    have hn2 : (D.tree b).size = 2 * m := by omega
    have hsl := slotSize_le D (.inr b)
    have hn : m ≤ Pg.N (p + 1) ^ 4 := by
      have : slotSize D (.inr b) = (D.tree b).size := rfl
      omega
    have hq0 := clkLayer_le D hS layer p hlay (argSrc hS (.inr b) 0)
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
        · by_cases hg0 : (nativeChainLayered D hS layer hLayer b).incoherency
              ((D.tree b).treeLinks ((nativeChainLayered D hS layer hLayer b).garden.sig 0)) = 0
          · exact Or.inr ⟨hg0, tree_coherent_at D hS layer hLayer p hcan b hg0⟩
          · exact Or.inl (Nat.one_le_iff_ne_zero.2 hg0)
    have h := ht C hC p m hp hn (D.tree b) (D.tree_wf b) hn2 (nativeChainLayered D hS layer hLayer b)
      (tree_decodes D hS layer hLayer b) (tree_noFlower D hS layer hLayer b)
      (fun j => tree_lone_card D hS layer hLayer b j)
      (fun a => hlay _) _ _ (tree_q'_le_q D hS layer hLayer p hlay b) hq0
      (tree_root_layer_le D hS layer hLayer p hlay b)
      (fun a ha => tree_lone_layer D hS layer hLayer b a ha) hcase (nativeChainProfiles D hS H b)
      (nativeChainB D hS B b) (chain_controlled D hS layer hLayer H B hctrl b) (treeG D g b) cψ hc1 (hg _)
      (treeQ D hS layer hLayer p b) (treeQ_spec D hS layer hLayer p b)
    refine (SupM.congr' h fun ts _ k => (slotFnNW_fw_tree D hS layer hLayer Pg.L Pg.γ Pg.δ H p g b ts k).symm).mono ?_
    exact hmono Kt _ _ (.inr b) (le_max_right _ _) (treeExp_le_slotNr D hS layer hLayer p b)
  · intro τ hτ s
    exact slotTs_mem_slotBox p (fun b => layer (D.coreBranch hS b).toNode) hS tt htt τ hτ s


end WaveTurbulence.Flower.Stage1WVine
