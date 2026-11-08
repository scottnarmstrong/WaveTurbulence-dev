/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsE.Engine

/-! # B3s-HELPER9 (MkSlotsE) 8: the outer centres sum to one, at one mode

For one outer slot mode (amplitudes `amp`, frequencies `frq`, hinge family `H`), with the one-mode assembly context
`modeCtx` (δ's `repIntCMKS_mode` context, as `ModeX.repIntCMKS_modeX`):

* `outerVal_modeψ_eq`: the per-mode outer form with an extra decoration weight `ψ` in the context form;
* `outerVal_mode_eq` / `outerVal_modeX_eq`: the per-mode outer form is `Σ_{ξh} ζ constWH ξh · kernel ξh` (δ's
  `value_eqHMD`), with `· chiX X` it is the restricted sum `Σ_{ξh} cindX X ξh · ζ constWH ξh · kernel ξh`
  (`DomX.value_eqHMDX`);
* `summable_mode_kernel`: the assembled terms are absolutely summable (as in δ's `repIntCMKF_of_asmHD`);
* **`hasSum_outerVal_modeX`**: `Σ_X outerValMμD … (Zw · chiX X) … = outerValMμD … Zw …` — every assembled index
  restricts to exactly one outer centre (`resC`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.MkSlots
  WaveTurbulence.Flower.MkSlotsS
open WaveTurbulence.Flower.MkSlotsI (CentredSlot chiX famX ChainPiece)
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsE

open scoped Classical

section Mode

variable {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL0 : 0 < P.L) (π : Stage1PieceMK P.d R)
    (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData π.Gsb P.d, D'.gapSpecification = π.gapSpecification →
      ∀ z : GenDecoration π.Gsb P.d roots 0,
        splicedGapIndicator π.Gsb D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    (Dom : Set (GBranch π.Gsb.tree → ℝ))
    (hsliceD : ∀ τ : {b : GBranch π.Gsb.tree // π.fix b = none} → ℝ,
      π.Gsb.extendFix π.fix τ ∈ Dom ↔ π.Gsb.extendFix π.fix τ ∈ fixLB π.Gsb π.layer tt π.fix π.lb)
    (amp : ReplacementSlot π.Gsb → Mom P.d → ℂ) (ctr : ReplacementSlot π.Gsb → Fin P.d → ℤ)
    (h1 : ∀ s k, ‖amp s k‖ ≤ 1) (h2 : ∀ s, SNorm (30 * P.d) 0 (amp s) ≤ 1)
    (h3 : ∀ p k, amp (Sum.inl p) k ≠ 0 → ‖k - latPt P.d (ctr (Sum.inl p))‖ ≤ 1)
    (frq : ReplacementSlot π.Gsb → Fin 2 → ℤ) {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot π.Gsb → Fin 2 → ClkSrc π.Gsb ⊕ J)
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (HkM : J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ)
    (H : HingeFam J P.d) (Mh : J → ℝ) (hMh : ∀ j c, ∑' l, H.w j c l ≤ Mh j)
    (hHk : HHkPropD π.toStage1PieceD tt base roots selSk Dom hclk hmom (fun j => HkM j (modLam frq route j)) H)
    (src : J → Fin 4 → HingeDarts π.Gsb π.Cs.hinges ⊕ Fin (2 * R))
    (src_dart : ∀ j i x, src j i = Sum.inl x → ∀ z : GenDecoration π.Gsb P.d roots 0,
      bondIndex π.Gsb z.1 x.1 = z.1 (hmom j i))
    (src_root : ∀ j i r, src j i = Sum.inr r → ∀ z : GenDecoration π.Gsb P.d roots 0, z.1 (hmom j i) = roots r)

/-- The one-mode assembly context (as in δ's `repIntCMKS_mode` and `ModeX.repIntCMKS_modeX`). -/
def modeCtx : AsmCtxH π.Gsb P.d :=
  { hS := hS, hd := hd1, L := P.L, hL := hL0, γ := P.γ, δ := P.δ, η := P.η, base := base, roots := roots,
    tt := tt, layer0 := dummyLayer π.Gsb tt, gs := π.gapSpecification, selSk := selSk, hgs := hgsp,
    fam := slotFamMode amp ctr (frqR frq route) h1 h2 h3, Cχ := Cchi P.d,
    hCpos := lt_of_lt_of_le zero_lt_one (Cchi_spec hd1).1, hC := (Cchi_spec hd1).2,
    Fn := fun s ts k => amp s k * fsPhase (frqR frq route s) ts, Box := fun _ => Set.univ,
    hFn := fun s ts _ k => by
      have := hasSum_fintype (fun _ : Unit => ((1 : ℝ) : ℂ) * amp s k * fsPhase (frqR frq route s) ts)
      simp [slotFamMode],
    hbox := fun _ _ _ => Set.mem_univ _,
    hinges := π.Cs.hinges, J := J, fJ := inferInstance, dJ := inferInstance, H := H,
    hmom := hmom, hclk := hclk, Hk := fun j => HkM j (modLam frq route j), Mh := Mh, hMh := hMh,
    hHk := fun κ hsel τ hτ j c hc =>
      hHk κ hsel τ (mem_of_mem_domFix π.Gsb π.layer tt π.fix π.lb Dom hsliceD
        (splicedTimeDomain_dummyLayer_sub π.Gsb tt π.layer π.fix π.lb hτ)) j c hc,
    src := src, src_dart := src_dart, src_root := src_root }

/-- The kernel of an assembled mode of the one-mode context. -/
abbrev modeKer (ξh : (modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk
    hmom HkM H Mh hMh hHk src src_dart src_root).Xi) : ℂ :=
  splicedKernelMK π.Gsb (DHMKD (modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route
    hclk hmom HkM H Mh hMh hHk src src_dart src_root) π.layer π.fix π.filt π.ind π.lb ξh)
    (modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom HkM H Mh hMh hHk
      src src_dart src_root).L
    (modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom HkM H Mh hMh hHk
      src src_dart src_root).γ
    (modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom HkM H Mh hMh hHk
      src src_dart src_root).η
    (modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom HkM H Mh hMh hHk
      src src_dart src_root).δ
    (modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom HkM H Mh hMh hHk
      src src_dart src_root).base
    (modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom HkM H Mh hMh hHk
      src src_dart src_root).roots

/-- The per-mode outer form with an extra decoration weight `ψ`, in the form of the one-mode context. -/
theorem outerVal_modeψ_eq (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j)
    (ψ : GenDecoration π.Gsb P.d roots 0 → ℂ) :
    outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
        (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0) * ψ z) hS
        (fixMeasure π.fix) amp frq route hclk hmom HkM =
      (coupling P.d P.L P.γ P.δ : ℂ) ^ π.Gsb.order * π.Gsb.zeta *
      ∑' κ : GenDecoration π.Gsb P.d roots 0, atomWF π.filt π.ind (cosetDecoration π.Gsb P.L base κ.1) *
        ((if selSk κ then ((splicedEpsilon π.Gsb π.Cs.hinges κ.1 : ℝ) : ℂ) else 0) *
          (ψ κ * ∫ τ, (domFix π.Gsb π.layer tt π.fix π.lb).indicator (fun τ =>
            phaseProd P.L P.γ P.δ π.Gsb (cosetDecoration π.Gsb P.L base κ.1) τ *
              ((modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom HkM H
                  Mh hMh hHk src src_dart src_root).skel κ τ *
                (modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom HkM H
                  Mh hMh hHk src src_dart src_root).hk κ τ)) τ
            ∂(fixMeasure π.fix))) := by
  unfold outerValMμD
  congr 1
  refine tsum_congr fun κ => ?_
  have hI0 := integral_indicator_congr_slice π.Gsb π.fix Dom (domFix π.Gsb π.layer tt π.fix π.lb)
    (fun τ => (hsliceD τ).trans (extendFix_mem_domFix_iff π.Gsb π.layer tt π.fix π.lb τ).symm)
    (fun τ => phaseProd P.L P.γ P.δ π.Gsb (cosetDecoration π.Gsb P.L base κ.1) τ *
        (∏ s, amp s (base + latticePoint P.L (κ.1 (slotNode hS s)))) * routedPhase frq route tt τ *
        ∏ j, HkM j (modLam frq route j) (fun c => clockOf π.Gsb tt τ (hclk j c))
          (fun c => base + latticePoint P.L (κ.1 (hmom j c))))
  have hI : ∫ τ, (domFix π.Gsb π.layer tt π.fix π.lb).indicator (fun τ =>
      phaseProd P.L P.γ P.δ π.Gsb (cosetDecoration π.Gsb P.L base κ.1) τ *
        (∏ s, amp s (base + latticePoint P.L (κ.1 (slotNode hS s)))) * routedPhase frq route tt τ *
        ∏ j, HkM j (modLam frq route j) (fun c => clockOf π.Gsb tt τ (hclk j c))
          (fun c => base + latticePoint P.L (κ.1 (hmom j c)))) τ ∂(fixMeasure π.fix) =
      ∫ τ, (domFix π.Gsb π.layer tt π.fix π.lb).indicator (fun τ =>
        phaseProd P.L P.γ P.δ π.Gsb (cosetDecoration π.Gsb P.L base κ.1) τ *
          ((modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom HkM H
              Mh hMh hHk src src_dart src_root).skel κ τ *
            (modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom HkM H
              Mh hMh hHk src src_dart src_root).hk κ τ)) τ
        ∂(fixMeasure π.fix) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    by_cases hτ : τ ∈ domFix π.Gsb π.layer tt π.fix π.lb
    · rw [Set.indicator_of_mem hτ, Set.indicator_of_mem hτ]
      show _ = phaseProd P.L P.γ P.δ π.Gsb (cosetDecoration π.Gsb P.L base κ.1) τ *
        ((∏ s, (amp s (base + latticePoint P.L (κ.1 (slotNode hS s))) *
            fsPhase (frqR frq route s) (slotTs hS tt τ s))) *
          ∏ j, HkM j (modLam frq route j) (fun c => clockOf π.Gsb tt τ (hclk j c))
            (fun c => base + latticePoint P.L (κ.1 (hmom j c))))
      rw [routedPhase_eq hS frq route hroute tt τ, Finset.prod_mul_distrib]
      ring
    · rw [Set.indicator_of_notMem hτ, Set.indicator_of_notMem hτ]
  rw [hI0, hI]
  generalize ∫ τ, (domFix π.Gsb π.layer tt π.fix π.lb).indicator (fun τ =>
        phaseProd P.L P.γ P.δ π.Gsb (cosetDecoration π.Gsb P.L base κ.1) τ *
          ((modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom HkM H
              Mh hMh hHk src src_dart src_root).skel κ τ *
            (modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom HkM H
              Mh hMh hHk src src_dart src_root).hk κ τ)) τ
        ∂(fixMeasure π.fix) = Y
  show ((splicedEpsilon π.Gsb π.Cs.hinges κ.1 : ℝ) : ℂ) *
      (atomWF π.filt π.ind (cosetDecoration π.Gsb P.L base κ.1) * (if selSk κ then 1 else 0) * ψ κ) * Y =
    atomWF π.filt π.ind (cosetDecoration π.Gsb P.L base κ.1) *
      ((if selSk κ then ((splicedEpsilon π.Gsb π.Cs.hinges κ.1 : ℝ) : ℂ) else 0) * (ψ κ * Y))
  by_cases hsel : selSk κ
  · simp only [hsel, ite_true]
    ring
  · simp only [hsel, ite_false, mul_zero, zero_mul]

variable (hfilt : ∀ a q, π.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1)

include hfilt hind in
/-- **The per-mode outer form is the assembled superposition** (δ's `value_eqHMD`). -/
theorem outerVal_mode_eq (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j) :
    outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
        (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0)) hS
        (fixMeasure π.fix) amp frq route hclk hmom HkM =
      ∑' ξh, (π.Gsb.zeta * (modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route
        hclk hmom HkM H Mh hMh hHk src src_dart src_root).constWH ξh) *
        modeKer hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom HkM H Mh hMh
          hHk src src_dart src_root ξh := by
  have hψ := outerVal_modeψ_eq hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk
    hmom HkM H Mh hMh hHk src src_dart src_root hroute (fun _ => 1)
  simp only [mul_one, one_mul] at hψ
  rw [hψ]
  have hHkD : HkOn (modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom HkM H Mh hMh hHk
      src src_dart src_root) (domFix π.Gsb π.layer tt π.fix π.lb) := fun κ hsel τ hτ j c hc =>
    hHk κ hsel τ (mem_of_mem_domFix π.Gsb π.layer tt π.fix π.lb Dom hsliceD hτ) j c hc
  exact value_eqHMD (modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom HkM H Mh hMh hHk
      src src_dart src_root) π.layer π.fix π.lb (fun _ _ _ => Set.mem_univ _) hHkD hfilt hind

include hfilt hind in
/-- **The per-mode outer form at the outer centre `X` is the restricted assembled superposition**
(`DomX.value_eqHMDX`). -/
theorem outerVal_modeX_eq (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j)
    (X : CentredSlot π.Gsb → (Fin P.d → ℤ)) :
    outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
        (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0) *
          chiX P.L base X z) hS
        (fixMeasure π.fix) amp frq route hclk hmom HkM =
      ∑' ξh, cindX X ξh.1.2 * ((π.Gsb.zeta * (modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2
        h3 frq route hclk hmom HkM H Mh hMh hHk src src_dart src_root).constWH ξh) *
        modeKer hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom HkM H Mh hMh
          hHk src src_dart src_root ξh) := by
  rw [outerVal_modeψ_eq hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk
    hmom HkM H Mh hMh hHk src src_dart src_root hroute (chiX P.L base X)]
  have hHkD : HkOn (modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom HkM H Mh hMh hHk
      src src_dart src_root) (domFix π.Gsb π.layer tt π.fix π.lb) := fun κ hsel τ hτ j c hc =>
    hHk κ hsel τ (mem_of_mem_domFix π.Gsb π.layer tt π.fix π.lb Dom hsliceD hτ) j c hc
  refine (value_eqHMDX (modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom HkM H Mh hMh hHk
      src src_dart src_root) π.layer π.fix π.lb (fun _ _ _ => Set.mem_univ _) hHkD hfilt hind X).trans ?_
  exact tsum_congr fun ξh => mul_assoc _ _ _

include hfilt hind in
/-- The assembled terms of the one-mode context are absolutely summable (as in δ's `repIntCMKF_of_asmHD`). -/
theorem summable_mode_kernel :
    Summable fun ξh => ‖(π.Gsb.zeta * (modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3
      frq route hclk hmom HkM H Mh hMh hHk src src_dart src_root).constWH ξh) *
      modeKer hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom HkM H Mh hMh
        hHk src src_dart src_root ξh‖ := by
  set A := modeCtx hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD amp ctr h1 h2 h3 frq route hclk hmom HkM H Mh
    hMh hHk src src_dart src_root with hA
  have hdbl := (sum_integral_sum_swap (fixMeasure π.fix) (gIHMD A (domFix π.Gsb π.layer A.tt π.fix π.lb) π.filt π.ind)
    (meas_gIHMD A (domFix π.Gsb π.layer A.tt π.fix π.lb) π.filt π.ind
      (measurableSet_domFix π.Gsb π.layer A.tt π.fix π.lb) (fixMeasure π.fix))
    (sum_lintegral_gIHMD_ne_top A (domFix π.Gsb π.layer A.tt π.fix π.lb) hfilt hind
      (measurableSet_domFix π.Gsb π.layer A.tt π.fix π.lb) (fixMeasure π.fix)
      (fixMeasure_domFix_le π.Gsb π.layer A.tt π.fix π.lb))).2
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξh => ?_)
    (hdbl.prod.mul_left (‖(coupling P.d A.L A.γ A.δ : ℂ) ^ π.Gsb.order‖))
  calc ‖π.Gsb.zeta * A.constWH ξh *
        splicedKernelMK π.Gsb (DHMKD A π.layer π.fix π.filt π.ind π.lb ξh) A.L A.γ A.η A.δ A.base A.roots‖
      = ‖A.constWH ξh *
          splicedKernelMK π.Gsb (DHMKD A π.layer π.fix π.filt π.ind π.lb ξh) A.L A.γ A.η A.δ A.base A.roots‖ := by
        rw [mul_assoc, norm_mul, norm_zeta, one_mul]
    _ = ‖(coupling P.d A.L A.γ A.δ : ℂ) ^ π.Gsb.order‖ *
        ‖∑' κ : GenDecoration π.Gsb P.d A.roots 0,
          ∫ τ, gIHMD A (domFix π.Gsb π.layer A.tt π.fix π.lb) π.filt π.ind ξh κ τ ∂(fixMeasure π.fix)‖ := by
        rw [← tsum_int_gIHMD A π.layer π.fix π.filt π.ind π.lb ξh, norm_mul]
    _ ≤ ‖(coupling P.d A.L A.γ A.δ : ℂ) ^ π.Gsb.order‖ *
        ∑' κ : GenDecoration π.Gsb P.d A.roots 0,
          ‖∫ τ, gIHMD A (domFix π.Gsb π.layer A.tt π.fix π.lb) π.filt π.ind ξh κ τ ∂(fixMeasure π.fix)‖ := by
        gcongr
        exact norm_tsum_le_tsum_norm (hdbl.prod_factor ξh)

end Mode

/-- **Every index restricts to exactly one outer centre**: for an absolutely summable `f` on assembled indices,
`Σ_X Σ_{ξh} cindX X ξh · f ξh = Σ_{ξh} f ξh`. -/
theorem hasSum_cindX {w d : ℕ} {S : Garden w} {Ξ : Type*} (nc : Ξ → GBranch S.tree → (Fin d → ℤ)) (f : Ξ → ℂ)
    (hf : Summable fun ξ => ‖f ξ‖) :
    HasSum (fun X : CentredSlot S → (Fin d → ℤ) => ∑' ξ, cindX X (nc ξ) * f ξ) (∑' ξ, f ξ) := by
  set g : (CentredSlot S → (Fin d → ℤ)) × Ξ → ℂ := fun q => cindX q.1 (nc q.2) * f q.2 with hg
  have hfib : ∀ ξ, HasSum (fun X : CentredSlot S → (Fin d → ℤ) => g (X, ξ)) (f ξ) := by
    intro ξ
    have h0 : ∀ X, X ≠ resC (nc ξ) → g (X, ξ) = 0 := by
      intro X hX
      simp only [hg, cindX]
      rw [if_neg (fun h => hX ((resX_iff X (nc ξ)).1 h).symm), zero_mul]
    have := hasSum_single (f := fun X => g (X, ξ)) (resC (nc ξ)) h0
    simpa [hg, cindX, resX_resC] using this
  have hfibn : ∀ ξ, HasSum (fun X : CentredSlot S → (Fin d → ℤ) => ‖g (X, ξ)‖) ‖f ξ‖ := by
    intro ξ
    have h0 : ∀ X, X ≠ resC (nc ξ) → ‖g (X, ξ)‖ = 0 := by
      intro X hX
      simp only [hg, cindX]
      rw [if_neg (fun h => hX ((resX_iff X (nc ξ)).1 h).symm), zero_mul, norm_zero]
    have := hasSum_single (f := fun X => ‖g (X, ξ)‖) (resC (nc ξ)) h0
    simpa [hg, cindX, resX_resC] using this
  -- summability on the product (swapped coordinates)
  set e := Equiv.prodComm (CentredSlot S → (Fin d → ℤ)) Ξ with he
  have hsw : Summable fun q : Ξ × (CentredSlot S → (Fin d → ℤ)) => ‖g (e.symm q)‖ := by
    refine (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2 ⟨fun ξ => (hfibn ξ).summable, ?_⟩
    exact hf.congr fun ξ => ((hfibn ξ).tsum_eq).symm
  have hgs : Summable g := by
    have : Summable fun q => ‖g q‖ := (e.symm.summable_iff (f := fun q => ‖g q‖)).mp hsw
    exact this.of_norm
  have htot : ∑' q, g q = ∑' ξ, f ξ := by
    have hgs' : Summable (fun q : Ξ × (CentredSlot S → (Fin d → ℤ)) => g (e.symm q)) :=
      (e.symm.summable_iff (f := g)).mpr hgs
    calc ∑' q, g q = ∑' q, g (e.symm q) := (e.symm.tsum_eq g).symm
      _ = ∑' ξ, ∑' X, g (e.symm (ξ, X)) := hgs'.tsum_prod
      _ = ∑' ξ, f ξ := tsum_congr fun ξ => (hfib ξ).tsum_eq
  rw [← htot]
  exact hgs.hasSum.prod_fiberwise fun X => (hgs.prod_factor X).hasSum

end WaveTurbulence.Flower.MkSlotsE
