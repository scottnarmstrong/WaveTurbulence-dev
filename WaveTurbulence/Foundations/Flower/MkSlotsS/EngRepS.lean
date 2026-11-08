/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsS.EngMom

/-! # B3s-HELPER4 (δ) S1 (4): pinned representations on a domain, with selection moments

Copies of B3s's `MkSlots/EngRep.lean` with (i) the time domain an arbitrary `Dom` agreeing with the kernel domain
`fixLB = splicedTimeDomainFix ∩ splicedLBDomain π.lb` (ruling R187) on the pinned slice (`hsliceD`), the hinge
expansions on `Dom` (`HHkPropD`), and (ii) the
selection moments of the kernel frequencies carried in the mass (`RepIntCMKS`, `RepIntCMKF`):

* `repIntCMKF_of_asmHD` (B3s `repIntCMK_of_asmH`): the assembled expansion of an outer form over `domFix` is a
  `RepIntCMKF` whose frequencies are the assembled frequencies `A.freqH`;
* `repIntCMKS_mode` (B3s `repIntCMK_mode`): one outer slot mode on `Dom`; its moment is that of the routed
  frequencies (`routedFreq`), provided no unit clock is a selected branch (`hselclk`);
* `repIntCMKS_vine_modes` (B3s `repIntCMK_vine_modes`): the INTERFACE v2 mode form with per-slot time weights
  `θs`, the moments paid by the slots adjacent to the selected branches (`modes_mass_sel_le`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Reg.Skeleton
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsS

/-- **The hinge superposition property on a time domain `Dom`** (main's `HHkProp`, RepVN2, with `Dom` in place of the
unpinned spliced domain). -/
abbrev HHkPropD {P : WTParams} {R : ℕ} {J : Type} (π : Stage1Piece P R) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (Dom : Set (GBranch π.Gsb.tree → ℝ))
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (Hk : J → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) (H : HingeFam J P.d) : Prop :=
  ∀ κ : GenDecoration π.Gsb P.d roots 0, selSk κ → ∀ τ ∈ Dom, ∀ j c,
    (∀ i, ‖(base + latticePoint P.L (κ.1 (hmom j i))) - latPt P.d (c i)‖ ≤ 1) →
    HasSum (fun l => (H.w j c l : ℂ) * H.a j c l (fun i => base + latticePoint P.L (κ.1 (hmom j i))) *
      fsPhase (H.m j c l) (fun i => clockOf π.Gsb tt τ (hclk j i)))
      (Hk j (fun i => clockOf π.Gsb tt τ (hclk j i)) (fun i => base + latticePoint P.L (κ.1 (hmom j i))))

/-- On the unpinned spliced domain, `HHkPropD` is main's `HHkProp`. -/
theorem hHkPropD_splicedTimeDomain {P : WTParams} {R : ℕ} {J : Type} (π : Stage1Piece P R)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration π.Gsb P.d roots 0 → Prop) (hclk : J → Fin 3 → ClkSrc π.Gsb)
    (hmom : J → Fin 4 → GNode π.Gsb.tree) (Hk : J → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) (H : HingeFam J P.d) :
    HHkPropD π tt base roots selSk (splicedTimeDomain π.Gsb π.layer tt) hclk hmom Hk H ↔
      HHkProp π tt base roots selSk hclk hmom Hk H :=
  Iff.rfl

open scoped Classical in
/-- **B3s's `repIntCMK_of_asmH` on `domFix`, recording the frequencies**: the assembled expansion of the outer form
against `fixMeasure π.fix` over `domFix π.Gsb π.layer A.tt π.fix π.lb` is a `RepIntCMKF` whose kernel frequencies are the
assembled frequencies `A.freqH ξh` (moment `≤ M`). The context `A` may have any `layer0`. -/
theorem repIntCMKF_of_asmHD {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (A : AsmCtxH π.Gsb P.d)
    (sel : Finset (GBranch π.Gsb.tree)) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hh : A.hinges = π.Cs.hinges) (hgs : A.gs = π.gapSpecification)
    (hL : A.L = P.L) (hγ : A.γ = P.γ) (hη : A.η = P.η) (hδ : A.δ = P.δ)
    (hbase : A.base = base) (hroots : A.roots = roots) (htt : A.tt = tt)
    (hbox : ∀ τ ∈ domFix π.Gsb π.layer A.tt π.fix π.lb, ∀ s, slotTs A.hS A.tt τ s ∈ A.Box s)
    (hHkD : HkOn A (domFix π.Gsb π.layer A.tt π.fix π.lb))
    (hfilt : ∀ a q, π.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1)
    (B : ℝ) (hB : 0 ≤ B)
    (hmass : ENNReal.ofReal (A.Cχ ^ Fintype.card (GBranch π.Gsb.tree)) *
      ((∏ s, ∑' l, ENNReal.ofReal (A.fam.w s l)) *
        ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ≥0∞)) * ∏ j, ENNReal.ofReal (A.Mh j) ≤
        ENNReal.ofReal B)
    (M : ℝ) (hM : ∀ ξh : A.Xi, momS sel (A.freqH ξh) ≤ M)
    (val : ℂ)
    (hval : val = (coupling P.d A.L A.γ A.δ : ℂ) ^ π.Gsb.order * π.Gsb.zeta *
      ∑' κ : GenDecoration π.Gsb P.d A.roots 0, atomWF π.filt π.ind (cosetDecoration π.Gsb A.L A.base κ.1) *
        ((if A.selSk κ then ((splicedEpsilon π.Gsb A.hinges κ.1 : ℝ) : ℂ) else 0) *
          ∫ τ, (domFix π.Gsb π.layer A.tt π.fix π.lb).indicator (fun τ =>
            phaseProd A.L A.γ A.δ π.Gsb (cosetDecoration π.Gsb A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ
            ∂(fixMeasure π.fix))) :
    RepIntCMKF π sel tt base roots val B M := by
  have hv := value_eqHMD A π.layer π.fix π.lb hbox hHkD hfilt hind
  rw [← hval] at hv
  -- the transported data of an assembled mode
  let toP : HingeDarts π.Gsb A.hinges → HingeDarts π.Gsb π.Cs.hinges := fun x => ⟨x.1, by rw [← hh]; exact x.2⟩
  let toA : HingeDarts π.Gsb π.Cs.hinges → HingeDarts π.Gsb A.hinges := fun x => ⟨x.1, by rw [hh]; exact x.2⟩
  let hingeT : A.Xi → (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ :=
    fun ξh K => A.hingeAmp ξh (fun x => K (toP x))
  have hK : ∀ ξh : A.Xi, splicedKernelMK π.Gsb (π.dataMK tt (fun x => cenS A.fam ξh.1 (slotOfDart A.hS x))
      (edgeS A.fam A.hS A.Cχ ξh.1) (hingeT ξh) (A.freqH ξh)) P.L P.γ P.η P.δ base roots =
      splicedKernelMK π.Gsb (DHMKD A π.layer π.fix π.filt π.ind π.lb ξh) A.L A.γ A.η A.δ A.base A.roots := by
    intro ξh
    rw [hL, hγ, hη, hδ, hbase, hroots]
    exact splicedKernelMK_congr_dataL π.Gsb _ _ _ _ _ _ _ _ rfl hh.symm rfl hgs.symm rfl htt.symm rfl rfl rfl rfl
      fun k => rfl
  -- summability of the weights
  have hw_sum : Summable fun ξh : A.Xi => ‖π.Gsb.zeta * A.constWH ξh‖ := by
    have h1 : ∑' ξh : A.Xi, ENNReal.ofReal ‖A.constWH ξh‖ ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top A.toAsmCtx.mass_ne_top (by simp)))
        (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top)) A.tsum_norm_constWH_le
    refine (ENNReal.summable_toReal h1).congr fun ξh => ?_
    rw [norm_mul, norm_zeta, one_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
  -- summability of the values
  have hdbl := (sum_integral_sum_swap (fixMeasure π.fix) (gIHMD A (domFix π.Gsb π.layer A.tt π.fix π.lb) π.filt π.ind)
    (meas_gIHMD A (domFix π.Gsb π.layer A.tt π.fix π.lb) π.filt π.ind
      (measurableSet_domFix π.Gsb π.layer A.tt π.fix π.lb) (fixMeasure π.fix))
    (sum_lintegral_gIHMD_ne_top A (domFix π.Gsb π.layer A.tt π.fix π.lb) hfilt hind
      (measurableSet_domFix π.Gsb π.layer A.tt π.fix π.lb) (fixMeasure π.fix)
      (fixMeasure_domFix_le π.Gsb π.layer A.tt π.fix π.lb))).2
  have hKs : Summable fun ξh : A.Xi => ‖π.Gsb.zeta * A.constWH ξh *
      splicedKernelMK π.Gsb (DHMKD A π.layer π.fix π.filt π.ind π.lb ξh) A.L A.γ A.η A.δ A.base A.roots‖ := by
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
  refine ⟨A.Xi, inferInstance, fun ξh => π.Gsb.zeta * A.constWH ξh,
    fun ξh x => cenS A.fam ξh.1 (slotOfDart A.hS x), fun ξh => edgeS A.fam A.hS A.Cχ ξh.1, hingeT,
    fun ξh => A.freqH ξh, ?_, ?_, hw_sum, ?_, hM, fun ξh => ?_⟩
  · simp_rw [hK]; exact hKs
  · rw [hv]
    exact tsum_congr fun ξh => by rw [hK]
  · have h1 : ENNReal.ofReal (∑' ξh : A.Xi, ‖π.Gsb.zeta * A.constWH ξh‖) =
        ∑' ξh : A.Xi, ENNReal.ofReal ‖π.Gsb.zeta * A.constWH ξh‖ :=
      ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hw_sum
    have h2 : ∑' ξh : A.Xi, ENNReal.ofReal ‖π.Gsb.zeta * A.constWH ξh‖ ≤ ENNReal.ofReal B := by
      calc _ = ∑' ξh : A.Xi, ENNReal.ofReal ‖A.constWH ξh‖ :=
            tsum_congr fun ξh => by rw [norm_mul, norm_zeta, one_mul]
        _ ≤ _ := A.tsum_norm_constWH_le
        _ ≤ _ := hmass
    exact (ENNReal.ofReal_le_ofReal_iff hB).1 (h1 ▸ h2)
  · -- amplitude bounds of the transported data
    have hb := A.splicedAmplitudeBounds_DH ξh
    refine ⟨hb.1, hb.2.1, fun K => A.norm_hingeAmp_le ξh _, fun K ⟨x, hx⟩ => ?_⟩
    exact hb.2.2.2 (fun y => K (toP y)) ⟨toA x, hx⟩

open scoped Classical in
/-- **One outer slot mode on a domain, with selection moments** (B3s's `repIntCMK_mode` with `Dom` and the
moments): the per-mode outer form `outerValMμD … Dom …` against `fixMeasure π.fix` with the weight
`pieceAtomW π · [selSk]` is a `RepIntCMKS` of mass `Cχ^b ballCard^n Π_j Mh_j · momS sel (routedFreq frq)`, when no
unit clock is a selected branch. -/
theorem repIntCMKS_mode {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL0 : 0 < P.L) (π : Stage1PieceMK P.d R)
    (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData π.Gsb P.d, D'.gapSpecification = π.gapSpecification →
      ∀ z : GenDecoration π.Gsb P.d roots 0,
        splicedGapIndicator π.Gsb D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    (Dom : Set (GBranch π.Gsb.tree → ℝ))
    (hsliceD : ∀ τ : {b : GBranch π.Gsb.tree // π.fix b = none} → ℝ,
      π.Gsb.extendFix π.fix τ ∈ Dom ↔ π.Gsb.extendFix π.fix τ ∈ fixLB π.Gsb π.layer tt π.fix π.lb)
    (hfilt : ∀ a q, π.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1)
    (amp : ReplacementSlot π.Gsb → Mom P.d → ℂ) (ctr : ReplacementSlot π.Gsb → Fin P.d → ℤ)
    (h1 : ∀ s k, ‖amp s k‖ ≤ 1) (h2 : ∀ s, SNorm (30 * P.d) 0 (amp s) ≤ 1)
    (h3 : ∀ p k, amp (Sum.inl p) k ≠ 0 → ‖k - latPt P.d (ctr (Sum.inl p))‖ ≤ 1)
    (frq : ReplacementSlot π.Gsb → Fin 2 → ℤ) {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot π.Gsb → Fin 2 → ClkSrc π.Gsb ⊕ J)
    (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j)
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (HkM : J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ)
    (H : HingeFam J P.d) (Mh : J → ℝ) (hMh : ∀ j c, ∑' l, H.w j c l ≤ Mh j)
    (hHk : HHkPropD π.toStage1PieceD tt base roots selSk Dom hclk hmom (fun j => HkM j (modLam frq route j)) H)
    (src : J → Fin 4 → HingeDarts π.Gsb π.Cs.hinges ⊕ Fin (2 * R))
    (src_dart : ∀ j i x, src j i = Sum.inl x → ∀ z : GenDecoration π.Gsb P.d roots 0,
      bondIndex π.Gsb z.1 x.1 = z.1 (hmom j i))
    (src_root : ∀ j i r, src j i = Sum.inr r → ∀ z : GenDecoration π.Gsb P.d roots 0, z.1 (hmom j i) = roots r)
    (sel : Finset (GBranch π.Gsb.tree)) (hselclk : ∀ v ∈ sel, ∀ j i, hclk j i ≠ Sum.inr v) :
    RepIntCMKS π sel tt base roots
      (outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
        (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0)) hS
        (fixMeasure π.fix) amp frq route hclk hmom HkM)
      ((Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) * ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) *
        ∏ j, Mh j) * momS sel (routedFreq hS route frq)) := by
  obtain ⟨hCge, hCspec⟩ := Cchi_spec hd1
  have hCpos : 0 < Cchi P.d := lt_of_lt_of_le zero_lt_one hCge
  have hdom : ∀ τ ∈ domFix π.Gsb π.layer tt π.fix π.lb, τ ∈ Dom := fun τ hτ =>
    mem_of_mem_domFix π.Gsb π.layer tt π.fix π.lb Dom hsliceD hτ
  let fam := slotFamMode amp ctr (frqR frq route) h1 h2 h3
  let A : AsmCtxH π.Gsb P.d :=
    { hS := hS, hd := hd1, L := P.L, hL := hL0, γ := P.γ, δ := P.δ, η := P.η, base := base, roots := roots,
      tt := tt, layer0 := dummyLayer π.Gsb tt, gs := π.gapSpecification, selSk := selSk, hgs := hgsp,
      fam := fam, Cχ := Cchi P.d, hCpos := hCpos, hC := hCspec,
      Fn := fun s ts k => amp s k * fsPhase (frqR frq route s) ts, Box := fun _ => Set.univ,
      hFn := fun s ts _ k => by
        have := hasSum_fintype (fun _ : Unit => ((1 : ℝ) : ℂ) * amp s k * fsPhase (frqR frq route s) ts)
        simp [fam, slotFamMode],
      hbox := fun _ _ _ => Set.mem_univ _,
      hinges := π.Cs.hinges, J := J, fJ := inferInstance, dJ := inferInstance, H := H,
      hmom := hmom, hclk := hclk, Hk := fun j => HkM j (modLam frq route j), Mh := Mh, hMh := hMh,
      hHk := fun κ hsel τ hτ j c hc =>
        hHk κ hsel τ (hdom τ (splicedTimeDomain_dummyLayer_sub π.Gsb tt π.layer π.fix π.lb hτ)) j c hc,
      src := src, src_dart := src_dart, src_root := src_root }
  have hHkD : HkOn A (domFix π.Gsb π.layer A.tt π.fix π.lb) := fun κ hsel τ hτ j c hc => hHk κ hsel τ (hdom τ hτ) j c hc
  have hB0 : 0 ≤ Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
      ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) * ∏ j, Mh j := by
    have hM : ∀ j, 0 ≤ Mh j := fun j => A.Mh_nonneg j (fun _ _ => 0)
    have hMp : 0 ≤ ∏ j, Mh j := Finset.prod_nonneg fun j _ => hM j
    exact mul_nonneg (mul_nonneg (pow_nonneg hCpos.le _) (by positivity)) hMp
  have hval : outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
        (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0)) hS
        (fixMeasure π.fix) amp frq route hclk hmom HkM =
      (coupling P.d A.L A.γ A.δ : ℂ) ^ π.Gsb.order * π.Gsb.zeta *
      ∑' κ : GenDecoration π.Gsb P.d A.roots 0, atomWF π.filt π.ind (cosetDecoration π.Gsb A.L A.base κ.1) *
        ((if A.selSk κ then ((splicedEpsilon π.Gsb A.hinges κ.1 : ℝ) : ℂ) else 0) *
          ∫ τ, (domFix π.Gsb π.layer A.tt π.fix π.lb).indicator (fun τ =>
            phaseProd A.L A.γ A.δ π.Gsb (cosetDecoration π.Gsb A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ
            ∂(fixMeasure π.fix)) := by
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
        ∫ τ, (domFix π.Gsb π.layer A.tt π.fix π.lb).indicator (fun τ =>
          phaseProd A.L A.γ A.δ π.Gsb (cosetDecoration π.Gsb A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ
          ∂(fixMeasure π.fix) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
      by_cases hτ : τ ∈ domFix π.Gsb π.layer tt π.fix π.lb
      · have hτ' : τ ∈ domFix π.Gsb π.layer A.tt π.fix π.lb := hτ
        rw [Set.indicator_of_mem hτ, Set.indicator_of_mem hτ']
        show _ = phaseProd P.L P.γ P.δ π.Gsb (cosetDecoration π.Gsb P.L base κ.1) τ *
          ((∏ s, (amp s (base + latticePoint P.L (κ.1 (slotNode hS s))) *
              fsPhase (frqR frq route s) (slotTs hS tt τ s))) *
            ∏ j, HkM j (modLam frq route j) (fun c => clockOf π.Gsb tt τ (hclk j c))
              (fun c => base + latticePoint P.L (κ.1 (hmom j c))))
        rw [routedPhase_eq hS frq route hroute tt τ, Finset.prod_mul_distrib]
        ring
      · have hτ' : τ ∉ domFix π.Gsb π.layer A.tt π.fix π.lb := hτ
        rw [Set.indicator_of_notMem hτ, Set.indicator_of_notMem hτ']
    rw [hI0, hI]
    generalize ∫ τ, (domFix π.Gsb π.layer A.tt π.fix π.lb).indicator (fun τ =>
          phaseProd A.L A.γ A.δ π.Gsb (cosetDecoration π.Gsb A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ
          ∂(fixMeasure π.fix) = X
    show ((splicedEpsilon π.Gsb π.Cs.hinges κ.1 : ℝ) : ℂ) *
        (atomWF π.filt π.ind (cosetDecoration π.Gsb P.L base κ.1) * (if selSk κ then 1 else 0)) * X =
      atomWF π.filt π.ind (cosetDecoration π.Gsb P.L base κ.1) *
        ((if selSk κ then ((splicedEpsilon π.Gsb π.Cs.hinges κ.1 : ℝ) : ℂ) else 0) * X)
    by_cases hsel : selSk κ
    · simp only [hsel, ite_true]
      ring
    · simp only [hsel, ite_false, mul_zero, zero_mul]
  -- the frequencies at the selected branches are the routed slot frequencies
  have hM : ∀ ξh : A.Xi, momS sel (A.freqH ξh) ≤ momS sel (routedFreq hS route frq) := by
    intro ξh
    refine le_of_eq (Finset.prod_congr rfl fun v hv => ?_)
    have h0 : (∑ j, ∑ i, if A.hclk j i = Sum.inr v then (A.H.m j _ (ξh.2 j) i : ℝ) else 0) = 0 :=
      Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => if_neg (hselclk v hv j i)
    have hf : A.freqH ξh v = routedFreq hS route frq v := by
      unfold AsmCtxH.freqH
      rw [h0, add_zero]
      rfl
    rw [hf]
  have hF := repIntCMKF_of_asmHD π A sel tt base roots rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _ _ _ => Set.mem_univ _) hHkD hfilt hind _ hB0 ?_ _ hM _ hval
  · exact hF.toRepIntCMKS (momS_nonneg _ _)
  have hmass : ∏ s, ∑' l : fam.Λ s, ENNReal.ofReal (A.fam.w s l) = 1 := by
    simp [A, fam, slotFamMode]
  rw [hmass, one_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_prod_of_nonneg (fun j _ => A.Mh_nonneg j (fun _ _ => 0)),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by have := hCpos.le; positivity)]

open scoped Classical in
/-- **The INTERFACE v2 mode form on a domain, with selection moments** (B3s's `repIntCMK_vine_modes`): per-slot time
weights `θs` with `θs s ≥ 2c + Σ_i selE s i`; the moments are paid by the slots adjacent to the selected branches at
the per-slot constant `9·selF s`. -/
theorem repIntCMKS_vine_modes {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL0 : 0 < P.L) (π : Stage1PieceMK P.d R)
    (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData π.Gsb P.d, D'.gapSpecification = π.gapSpecification →
      ∀ z : GenDecoration π.Gsb P.d roots 0,
        splicedGapIndicator π.Gsb D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    (Dom : Set (GBranch π.Gsb.tree → ℝ))
    (hsliceD : ∀ τ : {b : GBranch π.Gsb.tree // π.fix b = none} → ℝ,
      π.Gsb.extendFix π.fix τ ∈ Dom ↔ π.Gsb.extendFix π.fix τ ∈ fixLB π.Gsb π.layer tt π.fix π.lb)
    (hfilt : ∀ a q, π.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1)
    {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot π.Gsb → Fin 2 → ClkSrc π.Gsb ⊕ J)
    (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j)
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (src : J → Fin 4 → HingeDarts π.Gsb π.Cs.hinges ⊕ Fin (2 * R))
    (src_dart : ∀ j i x, src j i = Sum.inl x → ∀ z : GenDecoration π.Gsb P.d roots 0,
      bondIndex π.Gsb z.1 x.1 = z.1 (hmom j i))
    (src_root : ∀ j i r, src j i = Sum.inr r → ∀ z : GenDecoration π.Gsb P.d roots 0, z.1 (hmom j i) = roots r)
    (sel : Finset (GBranch π.Gsb.tree)) (hselclk : ∀ v ∈ sel, ∀ j i, hclk j i ≠ Sum.inr v)
    {I : Type} [Fintype I] (sgn : I → ℂ) (fam : I → SlotFam π.Gsb P.d) (μs : I → ReplacementSlot π.Gsb → ℝ≥0∞)
    (HkM : I → J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (θs : ReplacementSlot π.Gsb → ℝ) (hcθ : ∀ s, 2 * c + (selE route sel s 0 + selE route sel s 1) ≤ θs s)
    (hμ : ∀ i s, ∑' l, maxBracketPow (θs s) (half ((fam i).m s l)) * ENNReal.ofReal ((fam i).w s l) ≤ μs i s)
    (Kh : I → ℝ) (hKh : ∀ i, 0 ≤ Kh i)
    (hhinge : ∀ i (ξ : ∀ s, (fam i).Λ s), ∃ (H : HingeFam J P.d) (Mh : J → ℝ),
      (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
      HHkPropD π.toStage1PieceD tt base roots selSk Dom hclk hmom
        (fun j => HkM i j (modLam (fun s => (fam i).m s (ξ s)) route j)) H ∧
      ∏ j, Mh j ≤ Kh i * ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c)
    (Bi : I → ℝ) (hBi : ∀ i, 0 ≤ Bi i)
    (hBi' : ∀ i, ENNReal.ofReal (Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
        ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) * Kh i) *
        ∏ s, (ENNReal.ofReal (9 * selF route sel s) * μs i s) ≤ ENNReal.ofReal (Bi i)) :
    RepIntCMKS π sel tt base roots
      (∑ i, sgn i * ∑' ξ : ∀ s, (fam i).Λ s, (((∏ s, (fam i).w s (ξ s) : ℝ)) : ℂ) *
        outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
          (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0)) hS
          (fixMeasure π.fix) (fun s => (fam i).a s (ξ s)) (fun s => (fam i).m s (ξ s)) route hclk hmom (HkM i))
      (∑ i, ‖sgn i‖ * Bi i) := by
  obtain ⟨hCge, -⟩ := Cchi_spec hd1
  have hCpos : 0 < Cchi P.d := lt_of_lt_of_le zero_lt_one hCge
  set C0 : ℝ := Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
    ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) with hC0
  have hC00 : 0 ≤ C0 := by have := hCpos.le; positivity
  refine RepIntCMKS.finset_sum Finset.univ _ _ (fun i _ => mul_nonneg (norm_nonneg _) (hBi i)) (fun i _ => ?_)
  refine RepIntCMKS.smul ?_ (sgn i)
  have : ∀ s, Countable ((fam i).Λ s) := (fam i).cnt
  choose H Mh hMh hHk hMhb using hhinge i
  have hMh0 : ∀ ξ j, 0 ≤ Mh ξ j := fun ξ j => le_trans (tsum_nonneg fun l => (H ξ).w_nn j (fun _ _ => 0) l)
    (hMh ξ j (fun _ _ => 0))
  have hW : ∀ s l, 0 ≤ (fam i).w s l := (fam i).w_nn
  -- the mass of one mode
  set Bξ : (∀ s, (fam i).Λ s) → ℝ := fun ξ =>
    C0 * (∏ j, Mh ξ j) * momS sel (routedFreq hS route (fun s => (fam i).m s (ξ s))) with hBξ
  have hBξ0 : ∀ ξ, 0 ≤ Bξ ξ := fun ξ =>
    mul_nonneg (mul_nonneg hC00 (Finset.prod_nonneg fun j _ => hMh0 ξ j)) (momS_nonneg _ _)
  have hmode : ∀ ξ : ∀ s, (fam i).Λ s, RepIntCMKS π sel tt base roots
      (outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
        (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0)) hS
        (fixMeasure π.fix) (fun s => (fam i).a s (ξ s)) (fun s => (fam i).m s (ξ s)) route hclk hmom (HkM i))
      (Bξ ξ) := fun ξ =>
    repIntCMKS_mode hd1 hL0 π hS tt base roots selSk hgsp Dom hsliceD hfilt hind
      (fun s => (fam i).a s (ξ s)) (fun s => (fam i).n s (ξ s)) (fun s k => (fam i).a_one s _ k)
      (fun s => (fam i).a_snorm s _) (fun p k hk => (fam i).a_supp p _ k hk) (fun s => (fam i).m s (ξ s))
      route hroute hclk hmom (HkM i) (H ξ) (Mh ξ) (hMh ξ) (hHk ξ) src src_dart src_root sel hselclk
  -- the mode sum of the masses
  have hsumE : ∑' ξ : ∀ s, (fam i).Λ s,
      ENNReal.ofReal (‖(((∏ s, (fam i).w s (ξ s) : ℝ)) : ℂ)‖ * Bξ ξ) ≤ ENNReal.ofReal (Bi i) := by
    calc _ ≤ ∑' ξ : ∀ s, (fam i).Λ s, ENNReal.ofReal (‖(((∏ s, (fam i).w s (ξ s) : ℝ)) : ℂ)‖ *
          (C0 * Kh i * ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c) *
          ∏ s, ∏ i', (1 + |((fam i).m s (ξ s) i' : ℝ)|) ^ selE route sel s i') := by
          refine ENNReal.tsum_le_tsum fun ξ => ENNReal.ofReal_le_ofReal ?_
          have hmo := momS_routed_le hS route sel hroute (fun s => (fam i).m s (ξ s))
          have hpm : 0 ≤ ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c :=
            Finset.prod_nonneg fun j _ => by positivity
          have hMp : 0 ≤ ∏ j, Mh ξ j := Finset.prod_nonneg fun j _ => hMh0 ξ j
          have h1 : C0 * ∏ j, Mh ξ j ≤
              C0 * Kh i * ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c := by
            calc C0 * ∏ j, Mh ξ j ≤ C0 * (Kh i *
                  ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c) :=
                  mul_le_mul_of_nonneg_left (hMhb ξ) hC00
              _ = _ := by ring
          have key : Bξ ξ ≤
              (C0 * Kh i * ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c) *
                ∏ s, ∏ i', (1 + |((fam i).m s (ξ s) i' : ℝ)|) ^ selE route sel s i' :=
            mul_le_mul h1 hmo (momS_nonneg _ _) (mul_nonneg (mul_nonneg hC00 (hKh i)) hpm)
          calc ‖(((∏ s, (fam i).w s (ξ s) : ℝ)) : ℂ)‖ * Bξ ξ
              ≤ ‖(((∏ s, (fam i).w s (ξ s) : ℝ)) : ℂ)‖ *
                ((C0 * Kh i * ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c) *
                  ∏ s, ∏ i', (1 + |((fam i).m s (ξ s) i' : ℝ)|) ^ selE route sel s i') :=
                mul_le_mul_of_nonneg_left key (norm_nonneg _)
            _ = _ := by ring
      _ ≤ ENNReal.ofReal (C0 * Kh i) * ∏ s, (ENNReal.ofReal (9 * selF route sel s) * μs i s) :=
          modes_mass_sel_le route (fun s => (fam i).w s) hW (fun s => (fam i).m s) hc (selE route sel)
            (selE_nonneg route sel) θs hcθ (fun s => 9 * selF route sel s)
            (fun s => three_rpow_le_selF route sel s hc hc1) (μs i) (hμ i) (C0 * Kh i)
            (mul_nonneg hC00 (hKh i))
      _ ≤ _ := hBi' i
  have hne : ∑' ξ : ∀ s, (fam i).Λ s, ENNReal.ofReal (‖(((∏ s, (fam i).w s (ξ s) : ℝ)) : ℂ)‖ * Bξ ξ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsumE
  have hs : Summable fun ξ : ∀ s, (fam i).Λ s => ‖(((∏ s, (fam i).w s (ξ s) : ℝ)) : ℂ)‖ * Bξ ξ :=
    (ENNReal.summable_toReal hne).congr fun ξ =>
      ENNReal.toReal_ofReal (mul_nonneg (norm_nonneg _) (hBξ0 ξ))
  obtain ⟨-, hr⟩ := RepIntCMKS.tsum hS hL0 hfilt hind _ _ hs (fun ξ => (hmode ξ).smul _)
  refine hr.mono ?_
  have h1 : ENNReal.ofReal (∑' ξ : ∀ s, (fam i).Λ s, ‖(((∏ s, (fam i).w s (ξ s) : ℝ)) : ℂ)‖ * Bξ ξ) =
      ∑' ξ : ∀ s, (fam i).Λ s, ENNReal.ofReal (‖(((∏ s, (fam i).w s (ξ s) : ℝ)) : ℂ)‖ * Bξ ξ) :=
    ENNReal.ofReal_tsum_of_nonneg (fun ξ => mul_nonneg (norm_nonneg _) (hBξ0 ξ)) hs
  exact (ENNReal.ofReal_le_ofReal_iff (hBi i)).1 (h1 ▸ hsumE)

end WaveTurbulence.Flower.MkSlotsS
