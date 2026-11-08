/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.Core1
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.SlotTree
public import WaveTurbulence.Foundations.Stage1.Represents.RepSlots2
public import WaveTurbulence.Foundations.Stage1.Represents.RepPr7
public import WaveTurbulence.Foundations.Spine.IncoherentConstantMonotonicity
public import WaveTurbulence.Foundations.Spine.SourceProviders
public import WaveTurbulence.Foundations.Flower.IncTop.Gate

/-! # STAGE1W-O4: the weighted vine-free core and its prefix (row O4d, part 2)

* `slots_existW`: the per-slot superpositions of the weighted slot kernels of one profile (main's `slots_exist` with
  `couple_slot_targetW` / `tree_slot_targetW`), with masses carrying `cψ ^ slotNr`.
* `represents_noVine_coreW`: main's `represents_noVine_core` for the weighted value, at size `cψ^(3·order) s`.
* `NoVineRepresentsAtNW`, `noVineRepresentsAtNW_of_gate`: main's `NoVineRepresentsAtN` for the weighted value.
* `noVine_prefixNW`: its prefix, from main's two leafwise gates and the staged INC-TOP gate. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Flower.Stage1WNoVine
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  WaveTurbulence.VineEstS3.FS MeasureTheory Set WaveTurbulence.RegRedLeaf WaveTurbulence.RegRed
  WaveTurbulence.Represents WaveTurbulence.Flower.Stage1W WaveTurbulence.PL2330 WaveTurbulence.RedSplice
  WaveTurbulence.VineA
open scoped ENNReal

section Slots

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

theorem cplExp_le_slotNr (p : ℕ) (p' : SourcePair S) :
    cplExp (nativeCoupleLayered D hS layer hLayer p') (cplQ D hS layer hLayer p p' 0)
      (cplQ D hS layer hLayer p p' 1) ≤ slotNr D hS (.inl p') := by
  have h := card_embNodes_le (layeredReconstruction D hS layer hLayer) (nativeCoupleLayered D hS layer hLayer p')
    (fun a => (nativeCoupleForest D hS p').nodeEmbedding a) (fun j => ((nativeCoupleForest D hS p').root j).1)
    (fun a => rfl) p
  unfold cplExp cplNodes
  refine le_trans (le_of_eq ?_) (h.trans (le_of_eq rfl))
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  have e : ![cplQ D hS layer hLayer p p' 0, cplQ D hS layer hLayer p p' 1] x.1.1 = cplQ D hS layer hLayer p p' x.1.1 :=
    congrFun (fin2_vec (cplQ D hS layer hLayer p p')).symm x.1.1
  rw [e]
  rfl

theorem treeExp_le_slotNr (p : ℕ) (b : GBranch S.tree) :
    treeExp (nativeChainLayered D hS layer hLayer b) (treeQ D hS layer hLayer p b) ≤ slotNr D hS (.inr b) := by
  have h := card_embNodes_le (layeredReconstruction D hS layer hLayer) (nativeChainLayered D hS layer hLayer b)
    (chainContextNode D hS b) (fun _ => inflatedPosition S D.tree b.toNode) (fun a => rfl) p
  unfold treeExp treeNodes
  refine le_trans (le_of_eq ?_) (h.trans (le_of_eq rfl))
  congr 1

end Slots

/-- The explicit weighted slot constant (depends only on `d` and `η`). -/
noncomputable def KslotW (d : ℕ) (η : ℝ) : ℝ := max (KcplW d η) (KtrW d η)

/-- **Per-slot superpositions of the weighted slot kernels** (main's `slots_exist`, weighted). -/
theorem slots_existW (Pg : WTParams) (E : GateEnv Pg) (hinc : TopIncoherentDecayAtR Pg) :
    ∃ K : ℝ, 1 ≤ K ∧ K = KslotW Pg.d Pg.η ∧ ∀ (C : ℝ), 2 * Pg.C₁ ^ 2 * (1 + cLeib Pg.d (30 * Pg.d)) ≤ C →
      ∀ {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
        (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (p : ℕ),
        p < Pg.D → D.size ≤ Pg.N (p + 1) ^ 4 →
        IsCanonGC (p + 1) (layeredReconstruction D hS layer hLayer) →
        ∀ (tt : Fin w → ℝ), (∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) →
        ∀ (H : LeafProfiles w Pg.d) (B : (Fin w × TTree.Path) → NNReal),
        LeafwiseControlled (layeredReconstruction D hS layer hLayer) H B →
        ∀ (g : Fin w → Mom Pg.d → ℂ) (cψ : ℝ), 1 ≤ cψ → (∀ j, GPresented (32 * Pg.d) (g j) cψ) →
        ∃ Rep : SlotRep S hS Pg.d (fun b => layer (D.coreBranch hS b).toNode) tt,
          Rep.Fn = slotFnNW D hS Pg.L Pg.γ Pg.δ H (fwNode (layeredReconstruction D hS layer hLayer) p g)
            layer hLayer ∧
          ∀ s, Rep.μ s ≤ ENNReal.ofReal (K * cψ ^ slotNr D hS s * (C * Real.sqrt Pg.δ) ^ (slotSize D s) *
            Pg.L ^ (-(Pg.η ^ 8) * (slotIncoh D hS layer hLayer s : ℝ)) * slotLeaf D hS layer hLayer B s) := by
  obtain ⟨Kc, hKc1, hKce, hc⟩ := couple_slot_targetW Pg E hinc
  obtain ⟨Kt, hKt1, hKte, ht⟩ := tree_slot_targetW Pg E hinc
  refine ⟨max Kc Kt, le_trans hKc1 (le_max_left _ _), by rw [KslotW, hKce, hKte], fun C hC w S D hS layer hLayer p hp hN hcan tt htt H B hctrl
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
            cp := ?_, tr := ?_, hbox := ?_ }, rfl, fun s => le_rfl⟩
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
    refine (CenSup.congr' h fun ts _ k => (slotFnNW_fw_couple D hS layer hLayer Pg.L Pg.γ Pg.δ H p g p' ts k).symm).mono ?_
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
    refine (Sup.congr' h fun ts _ k => (slotFnNW_fw_tree D hS layer hLayer Pg.L Pg.γ Pg.δ H p g b ts k).symm).mono ?_
    exact hmono Kt _ _ (.inr b) (le_max_right _ _) (treeExp_le_slotNr D hS layer hLayer p b)
  · intro τ hτ s
    exact slotTs_mem_slotBox p (fun b => layer (D.coreBranch hS b).toNode) hS tt htt τ hτ s

/-- The constant of the weighted vine-free core (depends only on `d`, `η`, `C₁`). -/
noncomputable def CminFW (d : ℕ) (η C₁ : ℝ) : ℝ :=
  max (max 1 (2 * C₁ ^ 2 * (1 + cLeib d (30 * d)))) (Cchi d * (nodeBallCard d : ℝ) * KslotW d η ^ 2)

open scoped Classical in
/-- **The weighted vine-free core** (main's `represents_noVine_core` for the frontier-weighted value). -/
theorem represents_noVine_coreW (Pg : WTParams) (E : GateEnv Pg) (hinc : TopIncoherentDecayAtR Pg) :
    ∃ Cmin : ℝ, 1 ≤ Cmin ∧ Cmin = CminFW Pg.d Pg.η Pg.C₁ ∧ ∀ (C : ℝ), Cmin ≤ C →
      ∀ {R : ℕ} {S : Garden (2 * R)} (D : ReconstructionData S) (hS : S.IsPlain)
        (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (p : ℕ),
        p < Pg.D → D.size ≤ Pg.N (p + 1) ^ 4 →
        IsCanonGC (p + 1) (layeredReconstruction D hS layer hLayer) →
        ∀ (tt : Fin (2 * R) → ℝ), (∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) →
        ∀ (F : LeafFamily { Pg with C₁ := C } (2 * R)),
        F.Controlled (layeredReconstruction D hS layer hLayer) →
        ∀ (base : Mom Pg.d) (roots : Fin (2 * R) → (Fin Pg.d → ℤ))
          (gs : (v : GBranch S.tree) → Option (LocalGapSpecification S v))
          (selSk : GenDecoration S Pg.d roots 0 → Prop),
        (∀ D' : SplicedKernelData S Pg.d, D'.gapSpecification = gs → ∀ z : GenDecoration S Pg.d roots 0,
          splicedGapIndicator S D' Pg.L Pg.γ Pg.η base z.1 = if selSk z then 1 else 0) →
        ∀ (π : Stage1Piece { Pg with C₁ := C } R), π.Gsb = S → π.Cs.hinges = ∅ →
        HEq π.layer (fun b => layer (D.coreBranch hS b).toNode) → HEq π.gapSpecification gs →
        π.bsk = 0 → π.gsk = ∑ s, slotIncoh D hS layer hLayer s →
        ∀ (n : ℕ) (s : ℝ), F.size (layeredReconstruction D hS layer hLayer) ≤ s →
        n - S.order = D.size →
        ∀ (g : Fin (2 * R) → Mom Pg.d → ℂ) (cψ : ℝ), 1 ≤ cψ → (∀ j, GPresented (32 * Pg.d) (g j) cψ) →
        π.RepresentsInt n tt base roots (cψ ^ (3 * (D.garden hS).order) * s)
          (valueSelW F tt base roots (layeredReconstruction D hS layer hLayer)
            (fun κ => selSk (collapseGenDecoration D hS κ))
            (fwWeight p g base (layeredReconstruction D hS layer hLayer))) := by
  obtain ⟨K, hK1, hKe, hslot⟩ := slots_existW Pg E hinc
  refine ⟨max (max 1 (2 * Pg.C₁ ^ 2 * (1 + cLeib Pg.d (30 * Pg.d)))) (Cchi Pg.d * (nodeBallCard Pg.d : ℝ) * K ^ 2),
    le_max_of_le_left (le_max_left _ _), by rw [CminFW, hKe], ?_⟩
  intro C hC R S D hS layer hLayer p hp hN hcan tt htt F hctrl base roots gs selSk hgsp π hG hh hlay hgs
    hbsk hgsk n s hs hnrest g cψ hc1 hg
  have hC1 : 2 * Pg.C₁ ^ 2 * (1 + cLeib Pg.d (30 * Pg.d)) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC
  have hC2 : Cchi Pg.d * (nodeBallCard Pg.d : ℝ) * K ^ 2 ≤ C := le_trans (le_max_right _ _) hC
  have hx0 : 0 ≤ C * Real.sqrt Pg.δ := by
    have : 0 ≤ C := by nlinarith [E.hC1, cLeib_nonneg Pg.d (30 * Pg.d)]
    exact mul_nonneg this (Real.sqrt_nonneg _)
  have hgb : ∀ j x, ‖g j x‖ ≤ cψ := fun j x => GPresented.norm_le (hg j) (by linarith) x
  refine representsInt_of_slotsW (P := { Pg with C₁ := C }) E.hd1 E.hL1 D hS layer hLayer F hctrl tt base roots
    gs selSk hgsp π hG hh hlay hgs p g cψ hc1 hgb K (cψ ^ (3 * (D.garden hS).order)) hK1 (by positivity) hC2 hx0
    n s hs hbsk hnrest ?_
  intro i
  obtain ⟨Rep, hFn, hμ⟩ := hslot C hC1 D hS layer hLayer p hp hN hcan tt htt
    (F.H (layeredReconstruction D hS layer hLayer) i) (F.B (layeredReconstruction D hS layer hLayer) i)
    (hctrl i) g cψ hc1 hg
  refine ⟨Rep, hFn, slotSize D, slotIncoh D hS layer hLayer,
    fun s => cψ ^ slotNr D hS s * slotLeaf D hS layer hLayer (F.B (layeredReconstruction D hS layer hLayer) i) s,
    ?_, ?_, ?_, sum_slotSize D, hgsk.symm⟩
  · intro s
    have : 0 ≤ slotLeaf D hS layer hLayer (F.B (layeredReconstruction D hS layer hLayer) i) s := by
      cases s with
      | inl p' => exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
      | inr b => exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    positivity
  · intro s
    refine (hμ s).trans (le_of_eq ?_)
    congr 1
    ring
  · rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sum_slotNr, prod_slotLeaf]

/-! ### The vine-free successor pieces -/

open scoped Classical in
/-- `RepresentsInt` of every vine-free successor piece for the frontier-weighted value. -/
def NoVineRepresentsAtNW (P : WTParams) : Prop :=
  ∀ (R : ℕ) (S : Garden (2 * R)) (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (p : ℕ),
    p < P.D → D.size ≤ P.N (p + 1) ^ 4 →
    IsCanonGC (p + 1) (RegRed.layeredReconstruction D hS layer hLayer) →
    ∀ (tt : Fin (2 * R) → ℝ), (∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) →
    ∀ (F : LeafFamily P (2 * R)), F.Controlled (RegRed.layeredReconstruction D hS layer hLayer) →
    ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (σ : Prescription S),
    unitBlocks S σ = [] → S.molecule.IsMolecule →
    ∀ (n : ℕ) (s : ℝ), F.size (RegRed.layeredReconstruction D hS layer hLayer) ≤ s →
    n - S.order = D.size →
    ∀ (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ), 1 ≤ cψ → (∀ j, GPresented (32 * P.d) (g j) cψ) →
    Stage1Piece.RepresentsInt (P := P)
      (NormalizedSplice.stage1PieceOf P.d hS (RegRed.layeredReconstruction D hS layer hLayer)
        (D.garden_decodes hS) σ)
      n tt base roots (cψ ^ (3 * (D.garden hS).order) * s)
      (valueSelW F tt base roots (RegRed.layeredReconstruction D hS layer hLayer)
        (fun κ => NormalizedSplice.selOf (NormalizedSplice.GroupPrescription.ofPrescription σ) P.L P.γ P.η base
          (collapseGenDecoration D hS κ).1)
        (fwWeight p g base (RegRed.layeredReconstruction D hS layer hLayer)))

theorem noVineRepresentsAtNW_of_gate (Pg : WTParams) (E : GateEnv Pg) (hinc : TopIncoherentDecayAtR Pg) (C : ℝ)
    (hC : CminFW Pg.d Pg.η Pg.C₁ ≤ C) : NoVineRepresentsAtNW { Pg with C₁ := C } := by
  obtain ⟨Cmin, hC1, hCe, hcore⟩ := represents_noVine_coreW Pg E hinc
  intro R S D hS layer hLayer p hp hN hcan tt htt F hctrl base roots σ hσ hM n s hs hnrest g cψ hc1 hg
  rw [N_bumpC1] at hN
  have hL : Pg.L ≠ 0 := by have := E.hL1; positivity
  refine hcore C (hCe ▸ hC) D hS layer hLayer p hp hN hcan tt htt F hctrl base roots (gsCastN σ hσ)
    (fun z => NormalizedSplice.selOf (NormalizedSplice.GroupPrescription.ofPrescription σ) Pg.L Pg.γ Pg.η base z.1)
    (hgsp_noVineN hM hS σ hσ hL Pg.γ Pg.η base roots)
    (NormalizedSplice.stage1PieceOf Pg.d hS (RegRed.layeredReconstruction D hS layer hLayer)
      (D.garden_decodes hS) σ)
    (stSt_G_eq_of_unitBlocks_empty σ hσ)
    (stSt_hinges_eq_empty σ hσ) ?_ (heq_gapSpecN σ hσ) ?_ ?_ n s hs hnrest g cψ hc1 hg
  · have e : RegRed.coreLayer (RegRed.layeredReconstruction D hS layer hLayer) D hS (D.garden_decodes hS) =
        fun b => layer (D.coreBranch hS b).toNode := rfl
    show HEq ((stSt S σ).layer (RegRed.coreLayer (RegRed.layeredReconstruction D hS layer hLayer) D hS
      (D.garden_decodes hS))) _
    rw [e]
    exact heq_layer σ hσ _
  · exact bskOf_noVine σ hσ
  · show gskOf _ S σ _ = _
    rw [gskOf_noVine _ σ hσ, gregOf_eq_sum_slotIncoh D hS layer hLayer]

/-- The staged INC-TOP input is monotone in the large constants. -/
theorem topIncoherentDecayAtR_largeConstantMonotone : LargeConstantMonotone TopIncoherentDecayAtR := by
  intro P C₁ C₂ hC hC₂ hδ hL hCC hCC₂ hsource p hp n hn g cψ hc hg
  rw [N_largeConstants] at hn
  have hc0 : 0 ≤ P.C₁ := by linarith
  have hL0 : 0 ≤ P.L := by linarith
  have hreg := regBound_largeConstants_mono (C₂ := C₂) P hc0 hCC hδ.le hL0 n
  constructor
  · intro Q hw hsize LG hQ hlayer q q' hq hq' hroot hroot' hi H B hb
    refine ((hsource p hp n hn g cψ hc hg).1 Q hw hsize LG hQ hlayer q q' hq hq' hroot hroot' hi H B hb).trans ?_
    gcongr
    exact hreg _
  · intro X hw hsize LG hX hlayer q q' hqq' hqp hroot hlone hi H B hb
    refine ((hsource p hp n hn g cψ hc hg).2 X hw hsize LG hX hlayer q q' hqq' hqp hroot hlone hi H B hb).trans ?_
    gcongr
    exact hreg _

/-- **The weighted vine-free successor pieces at every admissible parameter record**, from main's leafwise gates and
the staged INC-TOP input (conditional helper: `hinc` is INC-TOP's target). -/
theorem noVine_prefixNW_of_incTop (hinc : TopIncoherentDecayGateR) : WTPrefix NoVineRepresentsAtNW := by
  have hboth : WTPrefix (fun P => LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) :=
    prefix_and Spine.leafwise_incoherent_decay Spine.leafwise_coherent_approximation
      leafwiseIncoherentDecay_largeConstantMonotone leafwiseCoherentApproximation30_largeConstantMonotone
  have hall : WTPrefix (fun P => (LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) ∧
      TopIncoherentDecayAtR P) :=
    prefix_and hboth hinc
      (leafwiseIncoherentDecay_largeConstantMonotone.and leafwiseCoherentApproximation30_largeConstantMonotone)
      topIncoherentDecayAtR_largeConstantMonotone
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hη⟩ := hall d hd γ hγ
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hg : 0 < g1 := by
    rw [hg1]
    refine lt_min (by linarith [hγ.1]) (lt_min one_pos ?_)
    have : 0 < 1 - γ := by linarith [hγ.2]
    nlinarith
  refine ⟨min η₀ (min (1 / 2) ((g1 / 2) ^ 2)), lt_min hη₀ (lt_min (by norm_num) (by positivity)), ?_⟩
  intro η hηm φin hφin τ hτ φ hsol
  have hη0 : η ≤ η₀ := hηm.2.trans (min_le_left _ _)
  have hη2 : η ≤ 1 / 2 := hηm.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη3 : η ≤ (g1 / 2) ^ 2 := hηm.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C₁g, hC₁g, ν₀, hν₀, hrest⟩ := hη η ⟨hηm.1, hη0⟩ φin hφin τ hτ φ hsol
  refine ⟨max C₁g (CminFW d η C₁g), hC₁g.trans (le_max_left _ _), ν₀, hν₀, ?_⟩
  intro ν hν
  obtain ⟨δ₀, hδ₀, hrest2⟩ := hrest ν hν
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂, hC₂, L₀, hL₀, hrest3⟩ := hrest2 δ hδ D hD htime
  refine ⟨C₂, hC₂, L₀, hL₀, ?_⟩
  intro L hL
  obtain ⟨⟨hincP, hcohP⟩, htopP⟩ := hrest3 L hL
  let Pg : WTParams := ⟨d, γ, η, φin, τ, φ, C₁g, ν, δ, D, C₂, L⟩
  have E : GateEnv Pg :=
    { hd1 := by show 1 ≤ d; omega
      hL1 := by show 1 ≤ L; linarith [hL₀.trans hL]
      hη0 := hηm.1.le
      hη := hη2
      hC1 := hC₁g
      hδ0 := hδ.1.le
      hκ := Represents.eta_pow_leN g1 η hg hηm.1 hη3 hη2
      hinc := hincP
      hcoh := hcohP }
  exact noVineRepresentsAtNW_of_gate Pg E htopP (max C₁g (CminFW d η C₁g)) (le_max_right _ _)

/-- **The weighted vine-free successor pieces**, unconditionally (INC-TOP's `topIncoherentDecayGateR`). -/
theorem noVine_prefixNW : WTPrefix NoVineRepresentsAtNW :=
  noVine_prefixNW_of_incTop IncTop.topIncoherentDecayGateR

end WaveTurbulence.Flower.Stage1WNoVine
