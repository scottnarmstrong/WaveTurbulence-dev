/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.OuterFix
public import WaveTurbulence.Foundations.Flower.MkSlots.SliceSb
public import WaveTurbulence.Foundations.Flower.SelRes.Triv
public import WaveTurbulence.Foundations.Stage1.Represents.RepVN10

/-! # B3s MK-SLOTS ENGINE (1): the pinned VINE-D engine, definitions and the count-measure representation

## Plan (thin pinned layer over main's VINE-D engine)

Target: `representsIntMK_of_vineModesFix` (file `EngVN`), the pinned twin of main's
`Represents.representsIntA_of_vineModes` (RepVN10): the per-mode outer forms `outerValMμ` against the pinned measure
`fixMeasure π.fix`, with the complex decoration weight `pieceAtomW · [selSk]`, give `π.RepresentsIntMK`.

The engine reads the time domain only through measurability, `μ (splicedTimeDomain) ≤ 1`, the hinge hypothesis on the
(unpinned) domain and the identification of the per-mode time integral with the kernel's. So:
* REUSED from main unchanged (domain-free): `AsmCtx`, `AsmCtxH` and their pointwise lemmas (`gIH`, `hasSum_gIH`,
  `norm_gIH_le`, `constWH`, `DH`, `hingeAmp`, `norm_hingeAmp_le`, `splicedAmplitudeBounds_DH`, `tsum_constWH_le`,
  `tsum_norm_constWH_le`, `tsum_bondProd_le`, `mass_ne_top`, `Mh_nonneg`, `continuous_timeFacH`), `slotFamMode`,
  `HHkProp`, `frqR`, `routedPhase_eq`, `modLam`, `modes_mass_le`, `vine_mass_le_repBound`, `Cchi_spec`,
  `sum_integral_sum_swap` (generic in the measure), `integral_count_eq_tsum`.
* COPIED (integral level, measure `fixMeasure fix`, decoration weight `atomWF filt ind`):
  - this file: `atomWF`/`pieceAtomW` (= `SplicedKernelDataMK.atomW`), `fixMeasure_splicedTimeDomain_le`,
    `integral_fixMeasure_indicator` (the time integral against `fixMeasure` is `splicedTimeIntegralMK` under the slice
    hypothesis), `splicedKernelMK_congr_data` (RepH13), `RepIntCMK` (RepRep1) with `toRepresentsIntMK` (RepVN5),
    closure lemmas `mono/zero/smul/add/finset_sum` (RepRep3) and `tsum` (RepH16, uniform bound from D7's
    `SelRes.norm_kernel_le_trivial`);
  - `EngInt`: `gIHM := atomWF ∘ coset · gIH`, `meas_gIHM`, `lintegral_gIHM_le`, `sum_lintegral_gIHM_ne_top`
    (RepH9/RepH10 with `μ`), `DHMK`, `tsum_int_gIHM` (RepH9), `value_eqHM` (RepH11);
  - `EngRep`: `repIntCMK_of_asmH` (RepH13), `repIntCMK_mode` (RepVN2, with the outer-form identification of
    RepOuterM2/RepH11), `repIntCMK_modes` (RepVN3), `repIntCMK_vine_modes` (RepVN7);
  - `EngVN`: `representsIntMK_of_vineModesFix` (RepVN10, plus the mass factor `L^{cP·d·nProt} ≥ 1`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic
open WaveTurbulence.Flower.MkDefs

namespace WaveTurbulence.Flower.MkSlots

variable {w d : ℕ}

/-! ## The atom weight -/

/-- The atom weight of the filters `filt` and the indicator `ind` (the body of `SplicedKernelDataMK.atomW`). -/
def atomWF {G : Garden w} (filt : GBranch G.tree → Option (ℝ × SchwartzMap ℝ ℂ))
    (ind : (GNode G.tree → Mom d) → ℝ) (k : GNode G.tree → Mom d) : ℂ :=
  (∏ a : GBranch G.tree, (filt a).elim 1 fun q => q.2 (omegaNode G k a / q.1)) * (ind k : ℂ)

theorem atomW_eq_atomWF {G : Garden w} (D : SplicedKernelDataMK G d) (k : GNode G.tree → Mom d) :
    D.atomW k = atomWF D.filt D.ind k := rfl

theorem norm_atomWF_le {G : Garden w} (filt : GBranch G.tree → Option (ℝ × SchwartzMap ℝ ℂ))
    (ind : (GNode G.tree → Mom d) → ℝ) (hfilt : ∀ a q, filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1)
    (hind : ∀ k, 0 ≤ ind k ∧ ind k ≤ 1) (k : GNode G.tree → Mom d) : ‖atomWF filt ind k‖ ≤ 1 := by
  unfold atomWF
  rw [norm_mul, norm_prod]
  have h1 : ∏ a, ‖(filt a).elim 1 fun q => q.2 (omegaNode G k a / q.1)‖ ≤ 1 := by
    refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun a _ => ?_
    rcases h : filt a with _ | q
    · simp
    · exact hfilt a q h _
  have h2 : ‖((ind k : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (hind k).1]; exact (hind k).2
  calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The atom weight of a marked piece: filters and indicator of `π` (`SplicedKernelDataMK.atomW` of `π.dataMK`, which
does not depend on the other data fields). -/
def pieceAtomW {d R : ℕ} (π : Stage1PieceMK d R) (k : GNode π.Gsb.tree → Mom d) : ℂ :=
  (∏ a, (π.filt a).elim 1 fun q => q.2 (omegaNode π.Gsb k a / q.1)) * (π.ind k : ℂ)

theorem pieceAtomW_eq_atomWF {d R : ℕ} (π : Stage1PieceMK d R) (k : GNode π.Gsb.tree → Mom d) :
    pieceAtomW π k = atomWF π.filt π.ind k := rfl

theorem pieceAtomW_eq_atomW {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (tt : Fin (2 * R) → ℝ)
    (center : GardenDart π.Gsb → Mom P.d) (edge : GardenDart π.Gsb → Mom P.d → ℂ)
    (hinge : (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ) (freq : GBranch π.Gsb.tree → ℝ)
    (k : GNode π.Gsb.tree → Mom P.d) :
    pieceAtomW π k = (π.dataMK tt center edge hinge freq).atomW k := rfl

/-! ## The pinned measure on the spliced time domain -/

theorem extendFix_eq_extendFixI_fun (G : Garden w) (fix : GBranch G.tree → Option ℝ) :
    G.extendFix fix = extendFixI fix := by
  funext τ b
  rcases h : fix b with _ | v
  · rw [WaveTurbulence.Flower.FlFace.extendFix_of_none fix τ b h, extendFixI_none fix τ h]
  · rw [WaveTurbulence.Flower.FlFace.extendFix_of_some fix τ b h, extendFixI_some fix τ h]

/-- The pinned measure of the spliced time domain is at most `1` (unit windows at free coordinates, Dirac mass `1` at
the pins). -/
theorem fixMeasure_splicedTimeDomain_le (G : Garden w) (layer : GBranch G.tree → ℕ) (rt : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) : fixMeasure fix (splicedTimeDomain G layer rt) ≤ 1 := by
  have hsub : splicedTimeDomain G layer rt ⊆
      Set.pi Set.univ (fun v : GBranch G.tree => Set.Icc (layer v : ℝ) (layer v + 1)) := by
    intro t ht v _
    exact ht.1 v
  refine (measure_mono hsub).trans ?_
  rw [fixMeasure, Measure.pi_pi]
  refine Finset.prod_le_one fun v _ => ?_
  rcases fix v with _ | x
  · simp [fixFactor, Real.volume_Icc]
  · simp only [fixFactor, Option.elim]
    exact prob_le_one

/-- **The time integral against the pinned measure is the pinned time integral**, when the unpinned and the pinned
domains agree on the pinned slice. -/
theorem integral_fixMeasure_indicator (G : Garden w) (D : SplicedKernelDataMK G d) (L γ δ : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ))
    (hslice : ∀ τ : {b : GBranch G.tree // D.fix b = none} → ℝ,
      G.extendFix D.fix τ ∈ splicedTimeDomain G D.layer D.rootTime ↔
        G.extendFix D.fix τ ∈ splicedTimeDomainFix G D.layer D.rootTime D.fix ∩ splicedLBDomain D.lb) :
    ∫ τ, (splicedTimeDomain G D.layer D.rootTime).indicator (fun t =>
        phaseProd L γ δ G (cosetDecoration G L base z) t *
          ∏ v : GBranch G.tree, Complex.exp ((Real.pi * D.frequency v * t v : ℝ) * Complex.I)) τ
        ∂(fixMeasure D.fix) =
      splicedTimeIntegralMK G D L γ δ base z := by
  rw [integral_fixMeasure]
  unfold splicedTimeIntegralMK
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  rw [← extendFix_eq_extendFixI_fun G D.fix]
  by_cases h : G.extendFix D.fix τ ∈ splicedTimeDomain G D.layer D.rootTime
  · rw [indicator_of_mem h, indicator_of_mem ((hslice τ).1 h)]
  · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h ((hslice τ).2 h'))]

/-- Without lower bounds (`lb = none`, R187) the intersection with `splicedLBDomain` is invisible. -/
theorem mem_inter_splicedLBDomain_none {G : Garden w} (s : Set (GBranch G.tree → ℝ)) (x : GBranch G.tree → ℝ) :
    x ∈ s ∩ splicedLBDomain (fun _ : GBranch G.tree => (none : Option ℝ)) ↔ x ∈ s := by
  simp [splicedLBDomain]

/-- **The slice hypothesis of the engine without lower bounds** (R187 form, `lb = none`), from `AdmissibleSb`. -/
theorem mem_splicedTimeDomain_slice_lb (G : Garden w) (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) (hA : AdmissibleSb G layer rootTime fix)
    (τ : {b : GBranch G.tree // fix b = none} → ℝ) :
    G.extendFix fix τ ∈ splicedTimeDomain G layer rootTime ↔
      G.extendFix fix τ ∈ splicedTimeDomainFix G layer rootTime fix ∩
        splicedLBDomain (fun _ : GBranch G.tree => (none : Option ℝ)) :=
  (mem_splicedTimeDomain_slice G layer rootTime fix hA τ).trans (mem_inter_splicedLBDomain_none _ _).symm

/-- The pinned spliced kernel depends on the data only through the layers, hinges, edge amplitudes, gap specification,
frequencies, root times, pins, filters, indicator and the values of the hinge amplitude at bond momenta (copy of main's
`splicedKernel_congr_data`, RepH13). -/
theorem splicedKernelMK_congr_data (G : Garden w) (D D' : SplicedKernelDataMK G d) (L γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (hl : D.layer = D'.layer) (hh : D.hinges = D'.hinges)
    (he : D.edgeAmplitude = D'.edgeAmplitude) (hg : D.gapSpecification = D'.gapSpecification)
    (hf : D.frequency = D'.frequency) (hr : D.rootTime = D'.rootTime) (hfix : D.fix = D'.fix)
    (hfilt : D.filt = D'.filt) (hind : D.ind = D'.ind) (hlb : D.lb = D'.lb)
    (hha : ∀ k : GardenDart G → Mom d, D.hingeAmplitude (fun x => k x.1) = D'.hingeAmplitude (fun x => k x.1)) :
    splicedKernelMK G D L γ η δ base roots = splicedKernelMK G D' L γ η δ base roots := by
  unfold splicedKernelMK
  congr 1
  refine tsum_congr fun z => ?_
  have h0 : D.atomW (cosetDecoration G L base z.1) = D'.atomW (cosetDecoration G L base z.1) := by
    rw [atomW_eq_atomWF, atomW_eq_atomWF, hfilt, hind]
  have h1 : splicedGapIndicator G D.toSplicedKernelData L γ η base z.1 =
      splicedGapIndicator G D'.toSplicedKernelData L γ η base z.1 := by
    unfold splicedGapIndicator; rw [hg]
  have h2 : splicedTimeIntegralMK G D L γ δ base z.1 = splicedTimeIntegralMK G D' L γ δ base z.1 := by
    unfold splicedTimeIntegralMK; rw [hl, hf, hr, hfix, hlb]
  have h3 : splicedEpsilon G D.hinges z.1 = splicedEpsilon G D'.hinges z.1 := by rw [hh]
  have h4 := hha (fun x => base + latticePoint L (bondIndex G z.1 x))
  rw [h0, h1, h2, h3, he]
  exact congrArg (fun c => _ * c * _) h4

/-! ## The count-measure form of `RepresentsIntMK` (pinned `RepIntC`, RepRep1) -/

/-- The count-measure form of `RepresentsIntMK`, with explicit mass bound `B`. -/
def RepIntCMK {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (val : ℂ) (B : ℝ) : Prop :=
  ∃ (Ξ : Type) (_ : Countable Ξ) (w : Ξ → ℂ) (ctr : Ξ → GardenDart π.Gsb → Mom P.d)
    (edge : Ξ → GardenDart π.Gsb → Mom P.d → ℂ)
    (hinge : Ξ → (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ) (freq : Ξ → GBranch π.Gsb.tree → ℝ),
    Summable (fun ξ => ‖w ξ * splicedKernelMK π.Gsb (π.dataMK tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots‖) ∧
    val = ∑' ξ, w ξ * splicedKernelMK π.Gsb (π.dataMK tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots ∧
    Summable (fun ξ => ‖w ξ‖) ∧ ∑' ξ, ‖w ξ‖ ≤ B ∧
    ∀ ξ, SplicedAmplitudeBounds π.Gsb (Stage1Piece.data π.toStage1PieceD tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))

/-- The bound of `RepresentsIntMK`. -/
def repBoundMK (P : WTParams) {R : ℕ} (π : Stage1PieceMK P.d R) (n : ℕ) (cP s : ℝ) : ℝ :=
  (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
    P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
      P.L ^ (cP * P.d * (π.nProt : ℝ)) * s

theorem RepIntCMK.toRepresentsIntMK {P : WTParams} {R : ℕ} {π : Stage1PieceMK P.d R} {tt : Fin (2 * R) → ℝ}
    {base : Mom P.d} {roots : Fin (2 * R) → (Fin P.d → ℤ)} {val : ℂ} {B : ℝ}
    (h : RepIntCMK π tt base roots val B) (n : ℕ) (cP s : ℝ) (hB : B ≤ repBoundMK P π n cP s) :
    π.RepresentsIntMK n cP tt base roots s val := by
  obtain ⟨Ξ, hc, w, ctr, edge, hinge, freq, h1, h2, h3, h4, h5⟩ := h
  let _ : MeasurableSpace Ξ := ⊤
  have : MeasurableSingletonClass Ξ := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  obtain ⟨hint, hint2⟩ := integral_count_eq_tsum _ h1
  obtain ⟨hint', hint2'⟩ := integral_count_real_eq_tsum _ h3.norm
  refine ⟨Ξ, inferInstance, Measure.count, w, ctr, edge, hinge, freq, hint, ?_, hint', ?_, h5⟩
  · rw [hint2]; exact h2
  · rw [hint2']; exact h4.trans hB

/-! ## Closure properties (RepRep3, RepH16) -/

section Closure

variable {P : WTParams} {R : ℕ} {π : Stage1PieceMK P.d R} {tt : Fin (2 * R) → ℝ} {base : Mom P.d}
  {roots : Fin (2 * R) → (Fin P.d → ℤ)}

theorem RepIntCMK.mono {val : ℂ} {B B' : ℝ} (h : RepIntCMK π tt base roots val B) (hB : B ≤ B') :
    RepIntCMK π tt base roots val B' := by
  obtain ⟨Ξ, hc, w, ctr, edge, hinge, freq, h1, h2, h3, h4, h5⟩ := h
  exact ⟨Ξ, hc, w, ctr, edge, hinge, freq, h1, h2, h3, h4.trans hB, h5⟩

theorem RepIntCMK.zero {B : ℝ} (hB : 0 ≤ B) : RepIntCMK π tt base roots 0 B := by
  refine ⟨Empty, inferInstance, fun e => e.elim, fun e => e.elim, fun e => e.elim, fun e => e.elim,
    fun e => e.elim, ?_, ?_, ?_, ?_, fun e => e.elim⟩
  · exact (hasSum_fintype _).summable
  · simp
  · exact (hasSum_fintype _).summable
  · simpa using hB

theorem RepIntCMK.smul {val : ℂ} {B : ℝ} (h : RepIntCMK π tt base roots val B) (c : ℂ) :
    RepIntCMK π tt base roots (c * val) (‖c‖ * B) := by
  obtain ⟨Ξ, hcnt, w, ctr, edge, hinge, freq, h1, h2, h3, h4, h5⟩ := h
  refine ⟨Ξ, hcnt, fun ξ => c * w ξ, ctr, edge, hinge, freq, ?_, ?_, ?_, ?_, h5⟩
  · simp_rw [mul_assoc]
    refine (h1.mul_left ‖c‖).congr fun ξ => ?_
    simp only [norm_mul]
  · rw [h2, ← tsum_mul_left]; exact tsum_congr fun ξ => by ring
  · simp_rw [norm_mul]; exact h3.mul_left _
  · simp_rw [norm_mul]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left h4 (norm_nonneg _)

theorem RepIntCMK.add {v₁ v₂ : ℂ} {B₁ B₂ : ℝ} (h₁ : RepIntCMK π tt base roots v₁ B₁)
    (h₂ : RepIntCMK π tt base roots v₂ B₂) : RepIntCMK π tt base roots (v₁ + v₂) (B₁ + B₂) := by
  obtain ⟨Ξ, hc, w, ctr, edge, hinge, freq, a1, a2, a3, a4, a5⟩ := h₁
  obtain ⟨Ξ', hc', w', ctr', edge', hinge', freq', b1, b2, b3, b4, b5⟩ := h₂
  refine ⟨Ξ ⊕ Ξ', inferInstance, Sum.elim w w', Sum.elim ctr ctr', Sum.elim edge edge',
    Sum.elim hinge hinge', Sum.elim freq freq', ?_, ?_, ?_, ?_, ?_⟩
  · exact Summable.sum _ a1 b1
  · rw [Summable.tsum_sum (f := fun ξ => (Sum.elim w w' ξ) * splicedKernelMK π.Gsb
      (π.dataMK tt (Sum.elim ctr ctr' ξ) (Sum.elim edge edge' ξ) (Sum.elim hinge hinge' ξ)
        (Sum.elim freq freq' ξ)) P.L P.γ P.η P.δ base roots) a1.of_norm b1.of_norm]
    rw [a2, b2]; rfl
  · exact Summable.sum _ a3 b3
  · rw [Summable.tsum_sum (f := fun ξ => ‖Sum.elim w w' ξ‖) a3 b3]
    exact add_le_add a4 b4
  · rintro (ξ | ξ)
    · exact a5 ξ
    · exact b5 ξ

theorem RepIntCMK.finset_sum {ι : Type*} (s : Finset ι) (val : ι → ℂ) (B : ι → ℝ) (hB : ∀ i ∈ s, 0 ≤ B i)
    (h : ∀ i ∈ s, RepIntCMK π tt base roots (val i) (B i)) :
    RepIntCMK π tt base roots (∑ i ∈ s, val i) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RepIntCMK.zero (π := π) (tt := tt) (base := base) (roots := roots) le_rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add
      (ih (fun i hi => hB i (Finset.mem_insert_of_mem hi)) (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- **Countable sums of pinned representations** (RepH16; the uniform kernel bound is D7's trivial bound). -/
theorem RepIntCMK.tsum (hS : π.Gsb.IsPlain) (hL : 0 < P.L)
    (hfilt : ∀ a q, π.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1)
    {ι : Type} [Countable ι] (val : ι → ℂ) (B : ι → ℝ)
    (hBs : Summable B) (h : ∀ i, RepIntCMK π tt base roots (val i) (B i)) :
    Summable val ∧ RepIntCMK π tt base roots (∑' i, val i) (∑' i, B i) := by
  choose Ξ hc w ctr edge hinge freq a1 a2 a3 a4 a5 using h
  have : ∀ i, Countable (Ξ i) := hc
  have hK0 : 0 ≤ ‖(coupling P.d P.L P.γ P.δ : ℂ)‖ ^ π.Gsb.order *
      (2 * P.L + 1) ^ (P.d * π.Gsb.molecule.bonds.card) := by positivity
  have hkb : ∀ p : Σ i, Ξ i, ‖splicedKernelMK π.Gsb (π.dataMK tt (ctr p.1 p.2) (edge p.1 p.2) (hinge p.1 p.2)
      (freq p.1 p.2)) P.L P.γ P.η P.δ base roots‖ ≤ ‖(coupling P.d P.L P.γ P.δ : ℂ)‖ ^ π.Gsb.order *
      (2 * P.L + 1) ^ (P.d * π.Gsb.molecule.bonds.card) := fun p =>
    WaveTurbulence.Flower.SelRes.norm_kernel_le_trivial hS _ (a5 p.1 p.2) hfilt hind hL _ _ _ _ _
  generalize ‖(coupling P.d P.L P.γ P.δ : ℂ)‖ ^ π.Gsb.order *
      (2 * P.L + 1) ^ (P.d * π.Gsb.molecule.bonds.card) = K at hK0 hkb
  have hWs : Summable fun p : Σ i, Ξ i => ‖w p.1 p.2‖ := by
    refine (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨fun i => a3 i, ?_⟩
    exact Summable.of_nonneg_of_le (fun i => tsum_nonneg fun _ => norm_nonneg _) a4 hBs
  have hWKs : Summable fun p : Σ i, Ξ i => ‖w p.1 p.2 * splicedKernelMK π.Gsb (π.dataMK tt (ctr p.1 p.2)
      (edge p.1 p.2) (hinge p.1 p.2) (freq p.1 p.2)) P.L P.γ P.η P.δ base roots‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) (hWs.mul_right K)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hkb p) (norm_nonneg _)
  have hsumval : ∑' p : Σ i, Ξ i, w p.1 p.2 * splicedKernelMK π.Gsb (π.dataMK tt (ctr p.1 p.2) (edge p.1 p.2)
      (hinge p.1 p.2) (freq p.1 p.2)) P.L P.γ P.η P.δ base roots = ∑' i, val i := by
    rw [hWKs.of_norm.tsum_sigma' (fun i => hWKs.of_norm.sigma_factor i)]
    exact tsum_congr fun i => (a2 i).symm
  have hvs : Summable val := (hWKs.of_norm.sigma).congr fun i => (a2 i).symm
  refine ⟨hvs, Σ i, Ξ i, inferInstance, fun p => w p.1 p.2, fun p => ctr p.1 p.2, fun p => edge p.1 p.2,
    fun p => hinge p.1 p.2, fun p => freq p.1 p.2, hWKs, hsumval.symm, hWs, ?_, fun p => a5 p.1 p.2⟩
  rw [hWs.tsum_sigma' (fun i => a3 i)]
  exact Summable.tsum_le_tsum a4 (Summable.of_nonneg_of_le (fun i => tsum_nonneg fun _ => norm_nonneg _) a4 hBs)
    hBs

end Closure

end WaveTurbulence.Flower.MkSlots
