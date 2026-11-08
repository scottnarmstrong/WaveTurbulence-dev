/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.FwNode
public import WaveTurbulence.Foundations.Flower.Stage1W.Defs
public import WaveTurbulence.Foundations.Stage1.Represents.RepNV4

/-! # STAGE1W-O4: the weighted core representation of a vine-free piece (row O4d, part 1)

Main's `repIntC_core`, `repIntC_core2` and `representsInt_of_slots` (RepNV2–4) with the frontier-weighted family value
`valueSelW … (fwWeight p g base LG)` of a reconstructed garden: the weighted leafwise skeleton reduction
(`valueSelW_skeleton_reduction`) turns it into the skeleton expression with the weighted slot kernels `slotFnNW`, and
per-slot superpositions of those kernels assemble into the representation exactly as in main.  The per-slot
weight costs enter through the leaf factors: `∏ lf_s = Λ · leafSize`, and the piece size becomes `Λ · s`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence.Induct
namespace WaveTurbulence.Flower.Stage1WNoVine
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  WaveTurbulence.VineEstS3.FS MeasureTheory Set WaveTurbulence.RegRedLeaf WaveTurbulence.RegRed
  WaveTurbulence.Represents WaveTurbulence.Flower.Stage1W
open scoped ENNReal

open scoped Classical in
/-- **The weighted family value of a reconstruction is the skeleton sum with the weighted slot kernels.** -/
theorem valueSelW_skeleton_reduction {P : WTParams} {R : ℕ} (F : LeafFamily P (2 * R))
    {S : Garden (2 * R)} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (hctrl : F.Controlled (layeredReconstruction D hS layer hLayer))
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration S P.d roots 0 → Prop)
    (p : ℕ) (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖g j x‖ ≤ cψ) :
    valueSelW F tt base roots (layeredReconstruction D hS layer hLayer)
        (fun κ => selSk (collapseGenDecoration D hS κ)) (fwWeight p g base (layeredReconstruction D hS layer hLayer)) =
      @Finset.sum (F.ι (layeredReconstruction D hS layer hLayer)) ℂ _
        (@Finset.univ _ (F.fin (layeredReconstruction D hS layer hLayer))) fun i =>
        ((F.sign (layeredReconstruction D hS layer hLayer) i : ℝ) : ℂ) *
          ((coupling P.d P.L P.γ P.δ : ℂ) ^ S.order * S.zeta *
            ∑' κ : GenDecoration S P.d roots 0, if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
              (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
                (fun τ => phaseProd P.L P.γ P.δ S (cosetDecoration S P.L base κ.1) τ *
                  reducedStarProductLeavesNW D hS P.L P.γ P.δ (F.H (layeredReconstruction D hS layer hLayer) i)
                    (fwNode (layeredReconstruction D hS layer hLayer) p g) layer hLayer tt base κ.1 τ) τ
            else 0) := by
  unfold valueSelW
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact kernelLeaves_skeleton_reduction_selNW D hS P.L P.γ P.δ (F.H (layeredReconstruction D hS layer hLayer) i)
    (fwNode (layeredReconstruction D hS layer hLayer) p g) cψ (by linarith)
    (norm_fwNode_le (layeredReconstruction D hS layer hLayer) p g cψ hc hg)
    layer hLayer tt base roots 0 ((hctrl i).summable_coset hd hL base) selSk

open scoped Classical in
/-- Main's `repIntC_core` for the frontier-weighted value. -/
theorem repIntC_coreW {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L)
    {S : Garden (2 * R)} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (F : LeafFamily P (2 * R)) (hctrl : F.Controlled (layeredReconstruction D hS layer hLayer))
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (gs : (v : GBranch S.tree) → Option (LocalGapSpecification S v))
    (selSk : GenDecoration S P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData S P.d, D'.gapSpecification = gs → ∀ z : GenDecoration S P.d roots 0,
      splicedGapIndicator S D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    (π : Stage1Piece P R) (hG : π.Gsb = S) (hh : π.Cs.hinges = ∅)
    (hlay : HEq π.layer (fun b => layer (D.coreBranch hS b).toNode))
    (hgs : HEq π.gapSpecification gs)
    (p : ℕ) (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖g j x‖ ≤ cψ)
    (Bi : F.ι (layeredReconstruction D hS layer hLayer) → ℝ) (hBi : ∀ i, 0 ≤ Bi i)
    (hslots : ∀ i, ∃ Rep : SlotRep S hS P.d (fun b => layer (D.coreBranch hS b).toNode) tt,
      Rep.Fn = slotFnNW D hS P.L P.γ P.δ (F.H (layeredReconstruction D hS layer hLayer) i)
        (fwNode (layeredReconstruction D hS layer hLayer) p g) layer hLayer ∧
      ∏ s, Rep.μ s ≤ ENNReal.ofReal (Bi i)) :
    RepIntC π tt base roots
      (valueSelW F tt base roots (layeredReconstruction D hS layer hLayer)
        (fun κ => selSk (collapseGenDecoration D hS κ)) (fwWeight p g base (layeredReconstruction D hS layer hLayer)))
      (Cchi P.d ^ Fintype.card (GBranch S.tree) * ((nodeBallCard P.d ^ ∑ j, (S.tree j).order : ℕ) : ℝ) *
        @Finset.sum (F.ι (layeredReconstruction D hS layer hLayer)) ℝ _
          (@Finset.univ _ (F.fin (layeredReconstruction D hS layer hLayer)))
          fun i => |F.sign (layeredReconstruction D hS layer hLayer) i| * Bi i) := by
  obtain ⟨Gsb, Cs, lad, play, gsp, gsk, bsk⟩ := π
  simp only at hG hh hlay hgs
  subst hG
  have hlay' := eq_of_heq hlay
  have hgs' := eq_of_heq hgs
  subst hlay' hgs'
  letI := F.fin (layeredReconstruction D hS layer hLayer)
  obtain ⟨hCge, hCspec⟩ := Cchi_spec hd1
  have hCpos : 0 < Cchi P.d := lt_of_lt_of_le zero_lt_one hCge
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  rw [valueSelW_skeleton_reduction F D hS layer hLayer hctrl hd1 hL1 tt base roots selSk p g cψ hc hg]
  refine RepIntC.mono (RepIntC.finset_sum (Finset.univ) _ (fun i =>
    ‖((F.sign (layeredReconstruction D hS layer hLayer) i : ℝ) : ℂ)‖ *
      (Cchi P.d ^ Fintype.card (GBranch Gsb.tree) * ((nodeBallCard P.d ^ ∑ j, (Gsb.tree j).order : ℕ) : ℝ) * Bi i))
    (fun i _ => by have := hBi i; positivity) (fun i _ => ?_)) (le_of_eq ?_)
  · obtain ⟨Rep, hFn, hmass⟩ := hslots i
    let A := asmOf hS hd1 P.L hL0 P.γ P.δ P.η base roots tt (fun b => layer (D.coreBranch hS b).toNode) gsp selSk hgsp
      (Cchi P.d) hCpos (hCspec) Rep
    have hskel : ∀ (κ : GenDecoration Gsb P.d roots 0) (τ : GBranch Gsb.tree → ℝ), A.skel κ τ =
        reducedStarProductLeavesNW D hS P.L P.γ P.δ (F.H (layeredReconstruction D hS layer hLayer) i)
          (fwNode (layeredReconstruction D hS layer hLayer) p g) layer hLayer tt base κ.1 τ := by
      intro κ τ
      show ∏ s, Rep.Fn s (slotTs hS tt τ s) (base + latticePoint P.L (κ.1 (slotNode hS s))) = _
      rw [hFn]
      exact prod_slotFnNW D hS P.L P.γ P.δ _ _ layer hLayer tt base κ.1 τ
    refine RepIntC.smul (repIntC_of_asm _ A tt base roots
      (Cchi P.d ^ Fintype.card (GBranch Gsb.tree) * ((nodeBallCard P.d ^ ∑ j, (Gsb.tree j).order : ℕ) : ℝ) * Bi i)
      hh rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ _ ?_) _
    · have := hBi i; positivity
    · have hμ := asmOf_mass hS hd1 P.L hL0 P.γ P.δ P.η base roots tt (fun b => layer (D.coreBranch hS b).toNode)
        gsp selSk hgsp (Cchi P.d) hCpos hCspec Rep
      show ENNReal.ofReal (Cchi P.d ^ Fintype.card (GBranch Gsb.tree)) * ((∏ s, ∑' l,
        ENNReal.ofReal (A.fam.w s l)) * ((nodeBallCard P.d ^ ∑ j, (Gsb.tree j).order : ℕ) : ℝ≥0∞)) ≤ _
      calc ENNReal.ofReal (Cchi P.d ^ Fintype.card (GBranch Gsb.tree)) * ((∏ s, ∑' l,
          ENNReal.ofReal (A.fam.w s l)) * ((nodeBallCard P.d ^ ∑ j, (Gsb.tree j).order : ℕ) : ℝ≥0∞))
          ≤ ENNReal.ofReal (Cchi P.d ^ Fintype.card (GBranch Gsb.tree)) * (ENNReal.ofReal (Bi i) *
            ((nodeBallCard P.d ^ ∑ j, (Gsb.tree j).order : ℕ) : ℝ≥0∞)) := by
            gcongr
            exact hμ.trans hmass
        _ = _ := by
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by have := hBi i; positivity),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1; push_cast; ring
    · show _ = (coupling P.d P.L P.γ P.δ : ℂ) ^ Gsb.order * Gsb.zeta * ∑' κ : GenDecoration Gsb P.d roots 0,
        (if selSk κ then ((epsDec Gsb κ.1 : ℝ) : ℂ) * ∫ τ, (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
          (fun τ => phaseProd P.L P.γ P.δ Gsb (cosetDecoration Gsb P.L base κ.1) τ * A.skel κ τ) τ else 0)
      refine congrArg _ (tsum_congr fun κ => ?_)
      split_ifs
      · congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
        simp only [Set.indicator]
        split_ifs
        · rw [hskel κ τ]
        · rfl
      · rfl
  · simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

open scoped Classical in
/-- Main's `repIntC_core2` with the weight costs in the leaf factors (`∏ lf_s = Λ · leafSize`). -/
theorem repIntC_core2W {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L)
    {S : Garden (2 * R)} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (F : LeafFamily P (2 * R)) (hctrl : F.Controlled (layeredReconstruction D hS layer hLayer))
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (gs : (v : GBranch S.tree) → Option (LocalGapSpecification S v))
    (selSk : GenDecoration S P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData S P.d, D'.gapSpecification = gs → ∀ z : GenDecoration S P.d roots 0,
      splicedGapIndicator S D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    (π : Stage1Piece P R) (hG : π.Gsb = S) (hh : π.Cs.hinges = ∅)
    (hlay : HEq π.layer (fun b => layer (D.coreBranch hS b).toNode))
    (hgs : HEq π.gapSpecification gs)
    (p : ℕ) (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖g j x‖ ≤ cψ)
    (K x e Λ : ℝ) (hK : 1 ≤ K) (hx0 : 0 ≤ x) (hΛ : 0 ≤ Λ) (nrest gsum : ℕ)
    (hslots : ∀ i, ∃ Rep : SlotRep S hS P.d (fun b => layer (D.coreBranch hS b).toNode) tt,
      Rep.Fn = slotFnNW D hS P.L P.γ P.δ (F.H (layeredReconstruction D hS layer hLayer) i)
        (fwNode (layeredReconstruction D hS layer hLayer) p g) layer hLayer ∧
      ∃ (sz g' : ReplacementSlot S → ℕ) (lf : ReplacementSlot S → ℝ), (∀ s, 0 ≤ lf s) ∧
        (∀ s, Rep.μ s ≤ ENNReal.ofReal (K * x ^ (sz s) * P.L ^ (-e * (g' s : ℝ)) * lf s)) ∧
        ∏ s, lf s = Λ * leafSizeProduct (layeredReconstruction D hS layer hLayer)
          (F.B (layeredReconstruction D hS layer hLayer) i) ∧
        ∑ s, sz s = nrest ∧ ∑ s, g' s = gsum) :
    RepIntC π tt base roots
      (valueSelW F tt base roots (layeredReconstruction D hS layer hLayer)
        (fun κ => selSk (collapseGenDecoration D hS κ)) (fwWeight p g base (layeredReconstruction D hS layer hLayer)))
      (Cchi P.d ^ Fintype.card (GBranch S.tree) * ((nodeBallCard P.d ^ ∑ j, (S.tree j).order : ℕ) : ℝ) *
        @Finset.sum (F.ι (layeredReconstruction D hS layer hLayer)) ℝ _
          (@Finset.univ _ (F.fin (layeredReconstruction D hS layer hLayer)))
          fun i => |F.sign (layeredReconstruction D hS layer hLayer) i| *
            (K ^ Fintype.card (ReplacementSlot S) * x ^ nrest * P.L ^ (-e * (gsum : ℝ)) *
              (Λ * leafSizeProduct (layeredReconstruction D hS layer hLayer)
                (F.B (layeredReconstruction D hS layer hLayer) i)))) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  choose Rep hFn sz g' lf hlf hμ hprod hsz hg' using hslots
  refine repIntC_coreW hd1 hL1 D hS layer hLayer F hctrl tt base roots gs selSk hgsp π hG hh hlay hgs p g cψ hc hg
    (fun i => K ^ Fintype.card (ReplacementSlot S) * x ^ nrest * P.L ^ (-e * (gsum : ℝ)) *
      (Λ * leafSizeProduct (layeredReconstruction D hS layer hLayer)
        (F.B (layeredReconstruction D hS layer hLayer) i))) (fun i => ?_)
    (fun i => ⟨Rep i, hFn i, ?_⟩)
  · have : 0 ≤ leafSizeProduct (layeredReconstruction D hS layer hLayer)
        (F.B (layeredReconstruction D hS layer hLayer) i) :=
      Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    have hK0 : 0 ≤ K := by linarith
    positivity
  · have hm : ∀ s, 0 ≤ K * x ^ (sz i s) * P.L ^ (-e * (g' i s : ℝ)) * lf i s :=
      fun s => by have := hlf i s; positivity
    calc ∏ s, (Rep i).μ s ≤ ∏ s, ENNReal.ofReal (K * x ^ (sz i s) * P.L ^ (-e * (g' i s : ℝ)) * lf i s) :=
          Finset.prod_le_prod (fun s _ => hμ i s)
      _ = ENNReal.ofReal (∏ s, (K * x ^ (sz i s) * P.L ^ (-e * (g' i s : ℝ)) * lf i s)) :=
          (ENNReal.ofReal_prod_of_nonneg fun s _ => hm s).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Finset.prod_mul_distrib, hprod i, ← hsz i, ← hg' i]
          have hK0 : 0 ≤ K := by linarith
          have hleaf : 0 ≤ Λ * leafSizeProduct (layeredReconstruction D hS layer hLayer)
              (F.B (layeredReconstruction D hS layer hLayer) i) :=
            mul_nonneg hΛ (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _)
          have := prod_slot_masses (fun s => K * x ^ (sz i s) * P.L ^ (-e * (g' i s : ℝ))) (sz i) (g' i) K x P.L e
            hK hx0 hL0 (fun s => ⟨by positivity, le_rfl⟩)
          exact mul_le_mul_of_nonneg_right this hleaf


open scoped Classical in
/-- Main's `representsInt_of_slots` for the frontier-weighted value, at size `Λ · s`. -/
theorem representsInt_of_slotsW {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L)
    {S : Garden (2 * R)} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (F : LeafFamily P (2 * R)) (hctrl : F.Controlled (layeredReconstruction D hS layer hLayer))
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (gs : (v : GBranch S.tree) → Option (LocalGapSpecification S v))
    (selSk : GenDecoration S P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData S P.d, D'.gapSpecification = gs → ∀ z : GenDecoration S P.d roots 0,
      splicedGapIndicator S D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    (π : Stage1Piece P R) (hG : π.Gsb = S) (hh : π.Cs.hinges = ∅)
    (hlay : HEq π.layer (fun b => layer (D.coreBranch hS b).toNode))
    (hgs : HEq π.gapSpecification gs)
    (p : ℕ) (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖g j x‖ ≤ cψ)
    (K Λ : ℝ) (hK : 1 ≤ K) (hΛ : 0 ≤ Λ) (hCbig : Cchi P.d * (nodeBallCard P.d : ℝ) * K ^ 2 ≤ P.C₁)
    (hx0 : 0 ≤ P.C₁ * Real.sqrt P.δ)
    (n : ℕ) (s : ℝ) (hs : F.size (layeredReconstruction D hS layer hLayer) ≤ s)
    (hbsk : π.bsk = 0) (hnrest : n - S.order = D.size)
    (hslots : ∀ i, ∃ Rep : SlotRep S hS P.d (fun b => layer (D.coreBranch hS b).toNode) tt,
      Rep.Fn = slotFnNW D hS P.L P.γ P.δ (F.H (layeredReconstruction D hS layer hLayer) i)
        (fwNode (layeredReconstruction D hS layer hLayer) p g) layer hLayer ∧
      ∃ (sz g' : ReplacementSlot S → ℕ) (lf : ReplacementSlot S → ℝ), (∀ s, 0 ≤ lf s) ∧
        (∀ s, Rep.μ s ≤ ENNReal.ofReal (K * (P.C₁ * Real.sqrt P.δ) ^ (sz s) *
          P.L ^ (-(P.η ^ 8) * (g' s : ℝ)) * lf s)) ∧
        ∏ s, lf s = Λ * leafSizeProduct (layeredReconstruction D hS layer hLayer)
          (F.B (layeredReconstruction D hS layer hLayer) i) ∧
        ∑ s, sz s = D.size ∧ ∑ s, g' s = π.gsk) :
    π.RepresentsInt n tt base roots (Λ * s)
      (valueSelW F tt base roots (layeredReconstruction D hS layer hLayer)
        (fun κ => selSk (collapseGenDecoration D hS κ)) (fwWeight p g base (layeredReconstruction D hS layer hLayer))) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  obtain ⟨hCge, -⟩ := Cchi_spec hd1
  have hb1 : (1 : ℝ) ≤ nodeBallCard P.d := by exact_mod_cast nodeBallCard_pos P.d
  obtain ⟨Gsb, Cs, lad, play, gsp, gsk, bsk⟩ := π
  simp only at hG hh hlay hgs hbsk hslots
  subst hG
  have hcore := repIntC_core2W hd1 hL1 D hS layer hLayer F hctrl tt base roots gs selSk hgsp
    ⟨Gsb, Cs, lad, play, gsp, gsk, bsk⟩ rfl hh hlay hgs p g cψ hc hg K (P.C₁ * Real.sqrt P.δ) (P.η ^ 8) Λ hK hx0 hΛ
    D.size gsk hslots
  refine RepIntC.toRepresentsInt hcore n (Λ * s) ?_
  letI := F.fin (layeredReconstruction D hS layer hLayer)
  have hbr : Fintype.card (GBranch Gsb.tree) = Gsb.order := WaveTurbulence.Mole.card_gbranch Gsb.tree
  have hslotsc : Fintype.card (ReplacementSlot Gsb) = 2 * Gsb.order + R := by
    have hpairs := sourcePair_card_twice Gsb hS
    unfold ReplacementSlot
    rw [Fintype.card_sum, hbr]
    omega
  have hord : ∑ j, (Gsb.tree j).order = Gsb.order := rfl
  rw [hbr, hslotsc, hord]
  show _ ≤ (P.C₁ * Real.sqrt P.δ) ^ (n - Gsb.order) * P.C₁ ^ (Gsb.order + 2 * R) *
    P.L ^ (-P.η ^ 8 * (gsk : ℝ) - P.η ^ 2 / 2 * (bsk : ℝ) + P.η ^ 7 * (Cs.hinges.card : ℝ)) * (Λ * s)
  rw [hnrest, hbsk, hh]
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero, sub_zero, add_zero]
  have hcabs := const_absorb (Cchi P.d) (nodeBallCard P.d : ℝ) K P.C₁ Gsb.order R hCge hb1 hK hCbig
  have hK0 : 0 ≤ K := by linarith
  have hleaf : ∀ i, 0 ≤ leafSizeProduct (layeredReconstruction D hS layer hLayer)
      (F.B (layeredReconstruction D hS layer hLayer) i) :=
    fun i => Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hA : 0 ≤ (P.C₁ * Real.sqrt P.δ) ^ D.size * P.L ^ (-P.η ^ 8 * (gsk : ℝ)) :=
    mul_nonneg (pow_nonneg hx0 _) (Real.rpow_nonneg hL0.le _)
  have hsum : ∑ i, |F.sign (layeredReconstruction D hS layer hLayer) i| *
      (K ^ (2 * Gsb.order + R) * (P.C₁ * Real.sqrt P.δ) ^ D.size * P.L ^ (-P.η ^ 8 * (gsk : ℝ)) *
        (Λ * leafSizeProduct (layeredReconstruction D hS layer hLayer)
          (F.B (layeredReconstruction D hS layer hLayer) i))) ≤
      K ^ (2 * Gsb.order + R) * ((P.C₁ * Real.sqrt P.δ) ^ D.size * P.L ^ (-P.η ^ 8 * (gsk : ℝ))) *
        (Λ * F.size (layeredReconstruction D hS layer hLayer)) := by
    unfold LeafFamily.size
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h0 : 0 ≤ K ^ (2 * Gsb.order + R) * (P.C₁ * Real.sqrt P.δ) ^ D.size *
        P.L ^ (-P.η ^ 8 * (gsk : ℝ)) * (Λ * leafSizeProduct (layeredReconstruction D hS layer hLayer)
          (F.B (layeredReconstruction D hS layer hLayer) i)) := by
      have := hleaf i
      have : 0 ≤ K ^ (2 * Gsb.order + R) := pow_nonneg hK0 _
      positivity
    calc _ ≤ 1 * (K ^ (2 * Gsb.order + R) * (P.C₁ * Real.sqrt P.δ) ^ D.size *
          P.L ^ (-P.η ^ 8 * (gsk : ℝ)) * (Λ * leafSizeProduct (layeredReconstruction D hS layer hLayer)
            (F.B (layeredReconstruction D hS layer hLayer) i))) :=
          mul_le_mul_of_nonneg_right (F.sign_abs_le _ i) h0
      _ = _ := by ring
  have hCh : 0 ≤ Cchi P.d ^ Gsb.order * (nodeBallCard P.d : ℝ) ^ Gsb.order := by
    have : 0 ≤ Cchi P.d := by linarith
    positivity
  have hs0 : 0 ≤ s := le_trans (Finset.sum_nonneg fun i _ => hleaf i) hs
  push_cast
  calc _ ≤ Cchi P.d ^ Gsb.order * (nodeBallCard P.d : ℝ) ^ Gsb.order *
        (K ^ (2 * Gsb.order + R) * ((P.C₁ * Real.sqrt P.δ) ^ D.size * P.L ^ (-P.η ^ 8 * (gsk : ℝ))) *
          (Λ * F.size (layeredReconstruction D hS layer hLayer))) := by
        exact mul_le_mul_of_nonneg_left hsum hCh
    _ ≤ Cchi P.d ^ Gsb.order * (nodeBallCard P.d : ℝ) ^ Gsb.order *
        (K ^ (2 * Gsb.order + R) * ((P.C₁ * Real.sqrt P.δ) ^ D.size * P.L ^ (-P.η ^ 8 * (gsk : ℝ))) *
          (Λ * s)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hs hΛ) (by positivity)) hCh
    _ = (Cchi P.d ^ Gsb.order * (nodeBallCard P.d : ℝ) ^ Gsb.order * K ^ (2 * Gsb.order + R)) *
        (((P.C₁ * Real.sqrt P.δ) ^ D.size * P.L ^ (-P.η ^ 8 * (gsk : ℝ))) * (Λ * s)) := by ring
    _ ≤ P.C₁ ^ (Gsb.order + 2 * R) * (((P.C₁ * Real.sqrt P.δ) ^ D.size * P.L ^ (-P.η ^ 8 * (gsk : ℝ))) *
        (Λ * s)) := by
        refine mul_le_mul_of_nonneg_right hcabs ?_
        positivity
    _ = _ := by ring

/-- `RepresentsInt` is monotone in the size. -/
theorem representsInt_mono_size {P : WTParams} {R : ℕ} (hC : 0 ≤ P.C₁) (hL : 0 ≤ P.L) {π : Stage1Piece P R}
    {n : ℕ} {tt : Fin (2 * R) → ℝ} {base : Mom P.d} {roots : Fin (2 * R) → (Fin P.d → ℤ)} {s s' : ℝ} {val : ℂ}
    (h : π.RepresentsInt n tt base roots s val) (hs : s ≤ s') : π.RepresentsInt n tt base roots s' val := by
  obtain ⟨Ξ, hm, μ, w, ctr, edge, hinge, freq, h1, h2, h3, h4, h5⟩ := h
  refine ⟨Ξ, hm, μ, w, ctr, edge, hinge, freq, h1, h2, h3, h4.trans ?_, h5⟩
  have hLp : 0 ≤ P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) :=
    Real.rpow_nonneg hL _
  have h0 : 0 ≤ (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) := by
    positivity
  exact mul_le_mul_of_nonneg_left hs h0

end WaveTurbulence.Flower.Stage1WNoVine
