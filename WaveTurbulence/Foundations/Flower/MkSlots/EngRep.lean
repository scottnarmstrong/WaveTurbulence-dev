/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.EngInt

/-! # B3s MK-SLOTS ENGINE (3): pinned representations of the per-mode outer forms

* `repIntCMK_of_asmH` (main RepH13 `repIntC_of_asmH`): the outer form of an assembly context with vine factors, against
  `fixMeasure π.fix` and with the atom weight of `π`, is a count-measure superposition of the pinned kernels
  `splicedKernelMK π.Gsb (π.dataMK …)`.
* `repIntCMK_mode` (main RepVN2 `repIntC_mode`): one outer slot mode, `outerValMμ` against `fixMeasure π.fix` with
  the weight `pieceAtomW π · [selSk]`.
* `repIntCMK_modes` (main RepVN3 `repIntC_modes`): countable weighted sums of modes.
* `repIntCMK_vine_modes` (main RepVN7 `repIntC_vine_modes`): the INTERFACE v2 mode form of a vine piece. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Reg.Skeleton
open WaveTurbulence.Flower.MkDefs
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlots

open scoped Classical in
/-- **RepH13, pinned**: the assembled expansion of the outer form against `fixMeasure π.fix` with the atom weight of
`π` is a `RepIntCMK` of mass `B` as soon as the explicit mass bound is `≤ B`. -/
theorem repIntCMK_of_asmH {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (A : AsmCtxH π.Gsb P.d)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hh : A.hinges = π.Cs.hinges) (hlay : A.layer0 = π.layer) (hgs : A.gs = π.gapSpecification)
    (hL : A.L = P.L) (hγ : A.γ = P.γ) (hη : A.η = P.η) (hδ : A.δ = P.δ)
    (hbase : A.base = base) (hroots : A.roots = roots) (htt : A.tt = tt)
    (hslice : ∀ τ : {b : GBranch π.Gsb.tree // π.fix b = none} → ℝ,
      π.Gsb.extendFix π.fix τ ∈ splicedTimeDomain π.Gsb A.layer0 A.tt ↔
        π.Gsb.extendFix π.fix τ ∈ splicedTimeDomainFix π.Gsb A.layer0 A.tt π.fix ∩ splicedLBDomain π.lb)
    (hfilt : ∀ a q, π.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1)
    (B : ℝ) (hB : 0 ≤ B)
    (hmass : ENNReal.ofReal (A.Cχ ^ Fintype.card (GBranch π.Gsb.tree)) *
      ((∏ s, ∑' l, ENNReal.ofReal (A.fam.w s l)) *
        ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ≥0∞)) * ∏ j, ENNReal.ofReal (A.Mh j) ≤
        ENNReal.ofReal B)
    (val : ℂ)
    (hval : val = (coupling P.d A.L A.γ A.δ : ℂ) ^ π.Gsb.order * π.Gsb.zeta *
      ∑' κ : GenDecoration π.Gsb P.d A.roots 0, atomWF π.filt π.ind (cosetDecoration π.Gsb A.L A.base κ.1) *
        ((if A.selSk κ then ((splicedEpsilon π.Gsb A.hinges κ.1 : ℝ) : ℂ) else 0) *
          ∫ τ, (splicedTimeDomain π.Gsb A.layer0 A.tt).indicator (fun τ =>
            phaseProd A.L A.γ A.δ π.Gsb (cosetDecoration π.Gsb A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ
            ∂(fixMeasure π.fix))) :
    RepIntCMK π tt base roots val B := by
  have hv := value_eqHM (A := A) (fix := π.fix) (hslice := hslice) (hfilt := hfilt) (hind := hind)
  rw [← hval] at hv
  -- the transported data of an assembled mode
  let toP : HingeDarts π.Gsb A.hinges → HingeDarts π.Gsb π.Cs.hinges := fun x => ⟨x.1, by rw [← hh]; exact x.2⟩
  let toA : HingeDarts π.Gsb π.Cs.hinges → HingeDarts π.Gsb A.hinges := fun x => ⟨x.1, by rw [hh]; exact x.2⟩
  let hingeT : A.Xi → (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ :=
    fun ξh K => A.hingeAmp ξh (fun x => K (toP x))
  have hK : ∀ ξh : A.Xi, splicedKernelMK π.Gsb (π.dataMK tt (fun x => cenS A.fam ξh.1 (slotOfDart A.hS x))
      (edgeS A.fam A.hS A.Cχ ξh.1) (hingeT ξh) (A.freqH ξh)) P.L P.γ P.η P.δ base roots =
      splicedKernelMK π.Gsb (DHMK A π.fix π.filt π.ind ξh π.lb) A.L A.γ A.η A.δ A.base A.roots := by
    intro ξh
    rw [hL, hγ, hη, hδ, hbase, hroots]
    exact splicedKernelMK_congr_data π.Gsb _ _ _ _ _ _ _ _ hlay.symm hh.symm rfl hgs.symm rfl htt.symm rfl rfl rfl rfl
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
  have hdbl := (sum_integral_sum_swap (fixMeasure π.fix) (gIHM A π.filt π.ind)
    (meas_gIHM A π.filt π.ind (fixMeasure π.fix))
    (sum_lintegral_gIHM_ne_top A hfilt hind (fixMeasure π.fix)
      (fixMeasure_splicedTimeDomain_le π.Gsb A.layer0 A.tt π.fix))).2
  have hKs : Summable fun ξh : A.Xi => ‖π.Gsb.zeta * A.constWH ξh *
      splicedKernelMK π.Gsb (DHMK A π.fix π.filt π.ind ξh π.lb) A.L A.γ A.η A.δ A.base A.roots‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξh => ?_)
      (hdbl.prod.mul_left (‖(coupling P.d A.L A.γ A.δ : ℂ) ^ π.Gsb.order‖))
    calc ‖π.Gsb.zeta * A.constWH ξh *
          splicedKernelMK π.Gsb (DHMK A π.fix π.filt π.ind ξh π.lb) A.L A.γ A.η A.δ A.base A.roots‖
        = ‖A.constWH ξh * splicedKernelMK π.Gsb (DHMK A π.fix π.filt π.ind ξh π.lb) A.L A.γ A.η A.δ A.base A.roots‖ := by
          rw [mul_assoc, norm_mul, norm_zeta, one_mul]
      _ = ‖(coupling P.d A.L A.γ A.δ : ℂ) ^ π.Gsb.order‖ *
          ‖∑' κ : GenDecoration π.Gsb P.d A.roots 0, ∫ τ, gIHM A π.filt π.ind ξh κ τ ∂(fixMeasure π.fix)‖ := by
          rw [← tsum_int_gIHM A π.fix π.filt π.ind π.lb hslice ξh, norm_mul]
      _ ≤ ‖(coupling P.d A.L A.γ A.δ : ℂ) ^ π.Gsb.order‖ *
          ∑' κ : GenDecoration π.Gsb P.d A.roots 0, ‖∫ τ, gIHM A π.filt π.ind ξh κ τ ∂(fixMeasure π.fix)‖ := by
          gcongr
          exact norm_tsum_le_tsum_norm (hdbl.prod_factor ξh)
  refine ⟨A.Xi, inferInstance, fun ξh => π.Gsb.zeta * A.constWH ξh,
    fun ξh x => cenS A.fam ξh.1 (slotOfDart A.hS x), fun ξh => edgeS A.fam A.hS A.Cχ ξh.1, hingeT,
    fun ξh => A.freqH ξh, ?_, ?_, hw_sum, ?_, fun ξh => ?_⟩
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
/-- **RepVN2, pinned: the per-mode representation of a vine piece.** One outer slot mode `(amp, frq)` with natural
routing and unit factors `HkM j (modLam frq route j)` superposed by the hinge families `H` (valid on the selected
decorations and the unpinned spliced domain), integrated against `fixMeasure π.fix` with the weight
`pieceAtomW π · [selSk]`, has a `RepIntCMK` representation of mass `Cχ^b ballCard^n Π_j Mh_j`. -/
theorem repIntCMK_mode {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL0 : 0 < P.L) (π : Stage1PieceMK P.d R)
    (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData π.Gsb P.d, D'.gapSpecification = π.gapSpecification →
      ∀ z : GenDecoration π.Gsb P.d roots 0,
        splicedGapIndicator π.Gsb D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    (hslice : ∀ τ : {b : GBranch π.Gsb.tree // π.fix b = none} → ℝ,
      π.Gsb.extendFix π.fix τ ∈ splicedTimeDomain π.Gsb π.layer tt ↔
        π.Gsb.extendFix π.fix τ ∈ splicedTimeDomainFix π.Gsb π.layer tt π.fix ∩ splicedLBDomain π.lb)
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
    (hHk : HHkProp π.toStage1PieceD tt base roots selSk hclk hmom (fun j => HkM j (modLam frq route j)) H)
    (src : J → Fin 4 → HingeDarts π.Gsb π.Cs.hinges ⊕ Fin (2 * R))
    (src_dart : ∀ j i x, src j i = Sum.inl x → ∀ z : GenDecoration π.Gsb P.d roots 0,
      bondIndex π.Gsb z.1 x.1 = z.1 (hmom j i))
    (src_root : ∀ j i r, src j i = Sum.inr r → ∀ z : GenDecoration π.Gsb P.d roots 0, z.1 (hmom j i) = roots r) :
    RepIntCMK π tt base roots
      (outerValMμ π.Gsb P.L P.γ P.δ base roots tt π.layer π.Cs.hinges
        (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0)) hS
        (fixMeasure π.fix) amp frq route hclk hmom HkM)
      (Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) * ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) *
        ∏ j, Mh j) := by
  obtain ⟨hCge, hCspec⟩ := Cchi_spec hd1
  have hCpos : 0 < Cchi P.d := lt_of_lt_of_le zero_lt_one hCge
  let fam := slotFamMode amp ctr (frqR frq route) h1 h2 h3
  let A : AsmCtxH π.Gsb P.d :=
    { hS := hS, hd := hd1, L := P.L, hL := hL0, γ := P.γ, δ := P.δ, η := P.η, base := base, roots := roots,
      tt := tt, layer0 := π.layer, gs := π.gapSpecification, selSk := selSk, hgs := hgsp, fam := fam,
      Cχ := Cchi P.d, hCpos := hCpos, hC := hCspec,
      Fn := fun s ts k => amp s k * fsPhase (frqR frq route s) ts, Box := fun _ => Set.univ,
      hFn := fun s ts _ k => by
        have := hasSum_fintype (fun _ : Unit => ((1 : ℝ) : ℂ) * amp s k * fsPhase (frqR frq route s) ts)
        simp [fam, slotFamMode],
      hbox := fun _ _ _ => Set.mem_univ _,
      hinges := π.Cs.hinges, J := J, fJ := inferInstance, dJ := inferInstance, H := H,
      hmom := hmom, hclk := hclk, Hk := fun j => HkM j (modLam frq route j), Mh := Mh, hMh := hMh,
      hHk := hHk, src := src, src_dart := src_dart, src_root := src_root }
  have hB0 : 0 ≤ Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
      ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) * ∏ j, Mh j := by
    have hM : ∀ j, 0 ≤ Mh j := fun j => A.Mh_nonneg j (fun _ _ => 0)
    have hMp : 0 ≤ ∏ j, Mh j := Finset.prod_nonneg fun j _ => hM j
    exact mul_nonneg (mul_nonneg (pow_nonneg hCpos.le _) (by positivity)) hMp
  have hval : outerValMμ π.Gsb P.L P.γ P.δ base roots tt π.layer π.Cs.hinges
        (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0)) hS
        (fixMeasure π.fix) amp frq route hclk hmom HkM =
      (coupling P.d A.L A.γ A.δ : ℂ) ^ π.Gsb.order * π.Gsb.zeta *
      ∑' κ : GenDecoration π.Gsb P.d A.roots 0, atomWF π.filt π.ind (cosetDecoration π.Gsb A.L A.base κ.1) *
        ((if A.selSk κ then ((splicedEpsilon π.Gsb A.hinges κ.1 : ℝ) : ℂ) else 0) *
          ∫ τ, (splicedTimeDomain π.Gsb A.layer0 A.tt).indicator (fun τ =>
            phaseProd A.L A.γ A.δ π.Gsb (cosetDecoration π.Gsb A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ
            ∂(fixMeasure π.fix)) := by
    unfold outerValMμ
    congr 1
    refine tsum_congr fun κ => ?_
    have hI : ∫ τ, (splicedTimeDomain π.Gsb π.layer tt).indicator (fun τ =>
        phaseProd P.L P.γ P.δ π.Gsb (cosetDecoration π.Gsb P.L base κ.1) τ *
          (∏ s, amp s (base + latticePoint P.L (κ.1 (slotNode hS s)))) * routedPhase frq route tt τ *
          ∏ j, HkM j (modLam frq route j) (fun c => clockOf π.Gsb tt τ (hclk j c))
            (fun c => base + latticePoint P.L (κ.1 (hmom j c)))) τ ∂(fixMeasure π.fix) =
        ∫ τ, (splicedTimeDomain π.Gsb A.layer0 A.tt).indicator (fun τ =>
          phaseProd A.L A.γ A.δ π.Gsb (cosetDecoration π.Gsb A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ
          ∂(fixMeasure π.fix) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
      by_cases hτ : τ ∈ splicedTimeDomain π.Gsb π.layer tt
      · have hτ' : τ ∈ splicedTimeDomain π.Gsb A.layer0 A.tt := hτ
        rw [Set.indicator_of_mem hτ, Set.indicator_of_mem hτ']
        show _ = phaseProd P.L P.γ P.δ π.Gsb (cosetDecoration π.Gsb P.L base κ.1) τ *
          ((∏ s, (amp s (base + latticePoint P.L (κ.1 (slotNode hS s))) *
              fsPhase (frqR frq route s) (slotTs hS tt τ s))) *
            ∏ j, HkM j (modLam frq route j) (fun c => clockOf π.Gsb tt τ (hclk j c))
              (fun c => base + latticePoint P.L (κ.1 (hmom j c))))
        rw [routedPhase_eq hS frq route hroute tt τ, Finset.prod_mul_distrib]
        ring
      · have hτ' : τ ∉ splicedTimeDomain π.Gsb A.layer0 A.tt := hτ
        rw [Set.indicator_of_notMem hτ, Set.indicator_of_notMem hτ']
    rw [hI]
    generalize ∫ τ, (splicedTimeDomain π.Gsb A.layer0 A.tt).indicator (fun τ =>
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
  refine repIntCMK_of_asmH π A tt base roots rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hslice hfilt hind _ hB0 ?_
    _ hval
  have hmass : ∏ s, ∑' l : fam.Λ s, ENNReal.ofReal (A.fam.w s l) = 1 := by
    simp [A, fam, slotFamMode]
  rw [hmass, one_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_prod_of_nonneg (fun j _ => A.Mh_nonneg j (fun _ _ => 0)),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by have := hCpos.le; positivity)]

section Modes

variable {P : WTParams} {R : ℕ} {π : Stage1PieceMK P.d R} {tt : Fin (2 * R) → ℝ} {base : Mom P.d}
  {roots : Fin (2 * R) → (Fin P.d → ℤ)}

/-- **RepVN3, pinned**: a countable weighted sum of per-mode representations. -/
theorem repIntCMK_modes (hS : π.Gsb.IsPlain) (hL : 0 < P.L)
    (hfilt : ∀ a q, π.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1)
    {ι : Type} [Countable ι] (W : ι → ℂ) (val : ι → ℂ)
    (B : ι → ℝ) (hB0 : ∀ ξ, 0 ≤ B ξ) (h : ∀ ξ, RepIntCMK π tt base roots (val ξ) (B ξ)) (Bt : ℝ) (hBt : 0 ≤ Bt)
    (hsum : ∑' ξ, ENNReal.ofReal (‖W ξ‖ * B ξ) ≤ ENNReal.ofReal Bt) :
    RepIntCMK π tt base roots (∑' ξ, W ξ * val ξ) Bt := by
  have hne : ∑' ξ, ENNReal.ofReal (‖W ξ‖ * B ξ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum
  have hs : Summable fun ξ => ‖W ξ‖ * B ξ :=
    (ENNReal.summable_toReal hne).congr fun ξ => ENNReal.toReal_ofReal (mul_nonneg (norm_nonneg _) (hB0 ξ))
  obtain ⟨-, hr⟩ := RepIntCMK.tsum hS hL hfilt hind (fun ξ => W ξ * val ξ) (fun ξ => ‖W ξ‖ * B ξ) hs
    (fun ξ => (h ξ).smul (W ξ))
  refine hr.mono ?_
  have h1 : ENNReal.ofReal (∑' ξ, ‖W ξ‖ * B ξ) = ∑' ξ, ENNReal.ofReal (‖W ξ‖ * B ξ) :=
    ENNReal.ofReal_tsum_of_nonneg (fun ξ => mul_nonneg (norm_nonneg _) (hB0 ξ)) hs
  exact (ENNReal.ofReal_le_ofReal_iff hBt).1 (h1 ▸ hsum)

end Modes

open scoped Classical in
/-- **RepVN7, pinned**: the INTERFACE v2 mode form of a vine piece, against `fixMeasure π.fix` with the weight
`pieceAtomW π · [selSk]`, is a `RepIntCMK` of mass `Σ_i |sgn_i| B_i`. -/
theorem repIntCMK_vine_modes {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL0 : 0 < P.L) (π : Stage1PieceMK P.d R)
    (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData π.Gsb P.d, D'.gapSpecification = π.gapSpecification →
      ∀ z : GenDecoration π.Gsb P.d roots 0,
        splicedGapIndicator π.Gsb D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    (hslice : ∀ τ : {b : GBranch π.Gsb.tree // π.fix b = none} → ℝ,
      π.Gsb.extendFix π.fix τ ∈ splicedTimeDomain π.Gsb π.layer tt ↔
        π.Gsb.extendFix π.fix τ ∈ splicedTimeDomainFix π.Gsb π.layer tt π.fix ∩ splicedLBDomain π.lb)
    (hfilt : ∀ a q, π.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1)
    {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot π.Gsb → Fin 2 → ClkSrc π.Gsb ⊕ J)
    (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j)
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (src : J → Fin 4 → HingeDarts π.Gsb π.Cs.hinges ⊕ Fin (2 * R))
    (src_dart : ∀ j i x, src j i = Sum.inl x → ∀ z : GenDecoration π.Gsb P.d roots 0,
      bondIndex π.Gsb z.1 x.1 = z.1 (hmom j i))
    (src_root : ∀ j i r, src j i = Sum.inr r → ∀ z : GenDecoration π.Gsb P.d roots 0, z.1 (hmom j i) = roots r)
    {I : Type} [Fintype I] (sgn : I → ℂ) (fam : I → SlotFam π.Gsb P.d) (μs : I → ReplacementSlot π.Gsb → ℝ≥0∞)
    (HkM : I → J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) {c θ : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hcθ : 2 * c ≤ θ)
    (hμ : ∀ i s, ∑' l, maxBracketPow θ (half ((fam i).m s l)) * ENNReal.ofReal ((fam i).w s l) ≤ μs i s)
    (Kh : I → ℝ) (hKh : ∀ i, 0 ≤ Kh i)
    (hhinge : ∀ i (ξ : ∀ s, (fam i).Λ s), ∃ (H : HingeFam J P.d) (Mh : J → ℝ),
      (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
      HHkProp π.toStage1PieceD tt base roots selSk hclk hmom
        (fun j => HkM i j (modLam (fun s => (fam i).m s (ξ s)) route j)) H ∧
      ∏ j, Mh j ≤ Kh i * ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c)
    (Bi : I → ℝ) (hBi : ∀ i, 0 ≤ Bi i)
    (hBi' : ∀ i, ENNReal.ofReal (Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
        ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) * Kh i) * ∏ s, (9 * μs i s) ≤
        ENNReal.ofReal (Bi i)) :
    RepIntCMK π tt base roots
      (∑ i, sgn i * ∑' ξ : ∀ s, (fam i).Λ s, (((∏ s, (fam i).w s (ξ s) : ℝ)) : ℂ) *
        outerValMμ π.Gsb P.L P.γ P.δ base roots tt π.layer π.Cs.hinges
          (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0)) hS
          (fixMeasure π.fix) (fun s => (fam i).a s (ξ s)) (fun s => (fam i).m s (ξ s)) route hclk hmom (HkM i))
      (∑ i, ‖sgn i‖ * Bi i) := by
  obtain ⟨hCge, -⟩ := Cchi_spec hd1
  have hCpos : 0 < Cchi P.d := lt_of_lt_of_le zero_lt_one hCge
  have hKc0 : ∀ i, 0 ≤ Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
      ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) * Kh i := fun i => by
    have := hKh i; have := hCpos.le; positivity
  refine RepIntCMK.finset_sum Finset.univ _ _ (fun i _ => mul_nonneg (norm_nonneg _) (hBi i)) (fun i _ => ?_)
  refine RepIntCMK.smul ?_ (sgn i)
  have : ∀ s, Countable ((fam i).Λ s) := (fam i).cnt
  choose H Mh hMh hHk hMhb using hhinge i
  have hMh0 : ∀ ξ j, 0 ≤ Mh ξ j := fun ξ j => le_trans (tsum_nonneg fun l => (H ξ).w_nn j (fun _ _ => 0) l)
    (hMh ξ j (fun _ _ => 0))
  have hW : ∀ s l, 0 ≤ (fam i).w s l := (fam i).w_nn
  refine repIntCMK_modes hS hL0 hfilt hind _ _
    (fun ξ => Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
      ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) * ∏ j, Mh ξ j)
    (fun ξ => mul_nonneg (mul_nonneg (pow_nonneg hCpos.le _) (by positivity))
      (Finset.prod_nonneg fun j _ => hMh0 ξ j))
    (fun ξ => repIntCMK_mode hd1 hL0 π hS tt base roots selSk hgsp hslice hfilt hind
      (fun s => (fam i).a s (ξ s)) (fun s => (fam i).n s (ξ s)) (fun s k => (fam i).a_one s _ k)
      (fun s => (fam i).a_snorm s _) (fun p k hk => (fam i).a_supp p _ k hk) (fun s => (fam i).m s (ξ s))
      route hroute hclk hmom (HkM i) (H ξ) (Mh ξ) (hMh ξ) (hHk ξ) src src_dart src_root) (Bi i) (hBi i) ?_
  calc ∑' ξ : ∀ s, (fam i).Λ s, ENNReal.ofReal (‖(((∏ s, (fam i).w s (ξ s) : ℝ)) : ℂ)‖ *
        (Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
          ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) * ∏ j, Mh ξ j))
      ≤ ∑' ξ : ∀ s, (fam i).Λ s, ENNReal.ofReal (‖(((∏ s, (fam i).w s (ξ s) : ℝ)) : ℂ)‖ *
        ((Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
          ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) * Kh i) *
          ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c)) := by
        refine ENNReal.tsum_le_tsum fun ξ => ENNReal.ofReal_le_ofReal ?_
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have h0 : 0 ≤ Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
            ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) := by have := hCpos.le; positivity
        calc _ ≤ Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
              ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) *
              (Kh i * ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c) :=
              mul_le_mul_of_nonneg_left (hMhb ξ) h0
          _ = _ := by ring
    _ ≤ ENNReal.ofReal (Cchi P.d ^ Fintype.card (GBranch π.Gsb.tree) *
          ((nodeBallCard P.d ^ ∑ j, (π.Gsb.tree j).order : ℕ) : ℝ) * Kh i) * ∏ s, (9 * μs i s) :=
        modes_mass_le route (fun s => (fam i).w s) hW (fun s => (fam i).m s) hc hc1 hcθ (μs i) (hμ i) _ (hKc0 i)
    _ ≤ _ := hBi' i

end WaveTurbulence.Flower.MkSlots
