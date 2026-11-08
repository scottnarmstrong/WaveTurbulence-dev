/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsE.AsmX
public import WaveTurbulence.Foundations.Flower.MkSlotsS.EngRepS

/-! # B3s-HELPER9 (MkSlotsE) 3: the restricted assembled expansion on a domain, its value and its mass

Copies of δ's `MkSlotsS.hasSum_gIHD`, `value_eqHMD` (EngDom.lean) and `repIntCMKF_of_asmHD` (EngRepS.lean) and of main's
`AsmCtxH.tsum_constWH_le` (RepH10) with the assembled modes restricted to the outer centre `X` (indicator
`cindX X ξh = [ξh's node centres restrict to X]`):

* `hasSum_gIHDX`: the restricted assembled summands sum to `chiX X · (ε · 1_Dom · phase · skel · hk)`;
* `value_eqHMDX`: the outer value with the decoration weight multiplied by `chiX X` is
  `Σ_{ξh} cindX X ξh · ζ · constWH ξh · kernel(ξh)` (Fubini as in δ's `value_eqHMD`);
* `tsum_constWHX_le`, `tsum_constWX_le`: the restricted mass `≤ Cχ^{#br} · Σ_ξ Π w · [x ∈ nodeCentreSet] · [x|centred = X]
  · Π_j Mh_j`;
* `repIntCMKF_of_asmHDX`: the restricted assembled expansion is a `RepIntCMKF` with the restricted mass. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlotsS
open WaveTurbulence.Flower.MkSlotsI (CentredSlot chiX)
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsE

variable {w d : ℕ}

/-- The indicator of the outer centre `X` on assembled indices (`x|centred = X`). -/
def cindX {S : Garden w} (X : CentredSlot S → (Fin d → ℤ)) (x : GBranch S.tree → (Fin d → ℤ)) : ℂ :=
  if ResX X x then 1 else 0

theorem norm_cindX_le {S : Garden w} (X : CentredSlot S → (Fin d → ℤ)) (x : GBranch S.tree → (Fin d → ℤ)) :
    ‖cindX X x‖ ≤ 1 := by
  unfold cindX; split_ifs <;> simp

theorem norm_cindX_mul {S : Garden w} (X : CentredSlot S → (Fin d → ℤ)) (x : GBranch S.tree → (Fin d → ℤ))
    (z : ℂ) : ‖cindX X x * z‖ = (if ResX X x then 1 else 0) * ‖z‖ := by
  unfold cindX; split_ifs <;> simp

section Dom
variable {S : Garden w} (A : AsmCtxH S d)

open scoped Classical in
/-- **δ's `hasSum_gIHD` restricted to the outer centre `X`.** -/
theorem hasSum_gIHDX (Dom : Set (GBranch S.tree → ℝ)) (hbox : ∀ τ ∈ Dom, ∀ s, slotTs A.hS A.tt τ s ∈ A.Box s)
    (hHkD : HkOn A Dom) (κ : GenDecoration S d A.roots 0) (τ : GBranch S.tree → ℝ)
    (X : CentredSlot S → (Fin d → ℤ)) :
    HasSum (fun ξh : A.Xi => cindX X ξh.1.2 * gIHD A Dom ξh κ τ)
      (chiX A.L A.base X κ * ((if A.selSk κ then ((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ) else 0) *
        Dom.indicator (fun τ =>
          phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ)) := by
  by_cases hτ : τ ∈ Dom
  · by_cases hsel : A.selSk κ
    · simp only [Set.indicator_of_mem hτ, if_pos hsel]
      have hs := hasSum_assembledHX A.fam A.hS A.hd A.Cχ A.hC A.hCpos A.L A.base A.roots A.tt A.Fn κ τ
        (fun s => A.hFn s _ (hbox τ hτ s) _) A.H A.hmom A.hclk A.Hk A.Mh A.hMh
        (fun j c hc => hHkD κ hsel τ hτ j c hc) X
      have h2 := hs.mul_left (((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ) *
        phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ)
      convert h2 using 1
      · funext ξh
        simp only [gIHD, if_pos hsel, Set.indicator_of_mem hτ, cindX]
        rw [A.slotTerm_mul_hingeTerm ξh κ τ]
        ring
      · unfold AsmCtx.skel AsmCtxH.hk; ring
    · simp only [gIHD, if_neg hsel, zero_mul, mul_zero]
      exact hasSum_zero
  · simp only [gIHD, Set.indicator_of_notMem hτ, mul_zero]
    exact hasSum_zero

section Pinned
variable (lay : GBranch S.tree → ℕ) (fix : GBranch S.tree → Option ℝ)
  {filt : GBranch S.tree → Option (ℝ × SchwartzMap ℝ ℂ)} {ind : (GNode S.tree → Mom d) → ℝ}
  (lb : GBranch S.tree → Option ℝ)

open scoped Classical in
/-- **δ's `value_eqHMD` restricted to the outer centre `X`**: the outer value with the extra decoration weight
`chiX X` is the restricted superposition of the assembled kernels. -/
theorem value_eqHMDX (hbox : ∀ τ ∈ domFix S lay A.tt fix lb, ∀ s, slotTs A.hS A.tt τ s ∈ A.Box s)
    (hHkD : HkOn A (domFix S lay A.tt fix lb))
    (hfilt : ∀ a q, filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ ind k ∧ ind k ≤ 1)
    (X : CentredSlot S → (Fin d → ℤ)) :
    (coupling d A.L A.γ A.δ : ℂ) ^ S.order * S.zeta *
      ∑' κ : GenDecoration S d A.roots 0, atomWF filt ind (cosetDecoration S A.L A.base κ.1) *
        ((if A.selSk κ then ((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ) else 0) *
          (chiX A.L A.base X κ * ∫ τ, (domFix S lay A.tt fix lb).indicator (fun τ =>
            phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ
            ∂(fixMeasure fix))) =
      ∑' ξh : A.Xi, (cindX X ξh.1.2 * (S.zeta * A.constWH ξh)) *
        splicedKernelMK S (DHMKD A lay fix filt ind lb ξh) A.L A.γ A.η A.δ A.base A.roots := by
  have hμ := fixMeasure_domFix_le S lay A.tt fix lb
  have hD := measurableSet_domFix S lay A.tt fix lb
  set Dm := domFix S lay A.tt fix lb with hDm
  set g : A.Xi → GenDecoration S d A.roots 0 → (GBranch S.tree → ℝ) → ℂ := fun ξh κ τ =>
    cindX X ξh.1.2 * gIHMD A Dm filt ind ξh κ τ with hg
  have hpt : ∀ κ τ, HasSum (fun ξh => g ξh κ τ) (atomWF filt ind (cosetDecoration S A.L A.base κ.1) *
      (chiX A.L A.base X κ * ((if A.selSk κ then ((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ) else 0) *
        Dm.indicator (fun τ =>
          phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ))) := by
    intro κ τ
    have h := (hasSum_gIHDX A Dm hbox hHkD κ τ X).mul_left (atomWF filt ind (cosetDecoration S A.L A.base κ.1))
    refine h.congr_fun fun ξh => ?_
    simp only [hg, gIHMD]
    ring
  have h1 : ∀ κ : GenDecoration S d A.roots 0, atomWF filt ind (cosetDecoration S A.L A.base κ.1) *
      ((if A.selSk κ then ((splicedEpsilon S A.hinges κ.1 : ℝ) : ℂ) else 0) *
        (chiX A.L A.base X κ * ∫ τ, Dm.indicator (fun τ =>
          phaseProd A.L A.γ A.δ S (cosetDecoration S A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ
          ∂(fixMeasure fix))) =
      ∫ τ, ∑' ξh, g ξh κ τ ∂(fixMeasure fix) := by
    intro κ
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only
    rw [(hpt κ τ).tsum_eq]
    ring
  simp_rw [h1]
  have hmeas : ∀ ξh κ, AEStronglyMeasurable (g ξh κ) (fixMeasure fix) := fun ξh κ =>
    aestronglyMeasurable_const.mul (meas_gIHMD A Dm filt ind hD (fixMeasure fix) ξh κ)
  have hbd : ∑' ξh, ∑' κ, ∫⁻ τ, ‖g ξh κ τ‖ₑ ∂(fixMeasure fix) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (sum_lintegral_gIHMD_ne_top A Dm hfilt hind hD (fixMeasure fix) hμ) ?_
    refine ENNReal.tsum_le_tsum fun ξh => ENNReal.tsum_le_tsum fun κ => lintegral_mono fun τ => ?_
    simp only [hg]
    rw [enorm_mul]
    calc ‖cindX X ξh.1.2‖ₑ * ‖gIHMD A Dm filt ind ξh κ τ‖ₑ ≤ 1 * ‖gIHMD A Dm filt ind ξh κ τ‖ₑ := by
          gcongr
          rw [← ofReal_norm, ← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (norm_cindX_le X _)
      _ = _ := one_mul _
  have hswap := (sum_integral_sum_swap (fixMeasure fix) g hmeas hbd).1
  rw [hswap, ← tsum_mul_left]
  refine tsum_congr fun ξh => ?_
  have h2 : ∑' κ : GenDecoration S d A.roots 0, ∫ τ, g ξh κ τ ∂(fixMeasure fix) =
      cindX X ξh.1.2 * ∑' κ : GenDecoration S d A.roots 0,
        ∫ τ, gIHMD A Dm filt ind ξh κ τ ∂(fixMeasure fix) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun κ => integral_const_mul _ _
  have h3 := tsum_int_gIHMD A lay fix filt ind lb ξh
  rw [h2]
  calc (coupling d A.L A.γ A.δ : ℂ) ^ S.order * S.zeta * (cindX X ξh.1.2 *
        ∑' κ : GenDecoration S d A.roots 0, ∫ τ, gIHMD A Dm filt ind ξh κ τ ∂(fixMeasure fix))
      = cindX X ξh.1.2 * S.zeta * ((coupling d A.L A.γ A.δ : ℂ) ^ S.order *
          ∑' κ : GenDecoration S d A.roots 0, ∫ τ, gIHMD A Dm filt ind ξh κ τ ∂(fixMeasure fix)) := by ring
    _ = _ := by rw [h3]; ring

end Pinned

open scoped Classical in
/-- **Main's `tsum_constWH_le` restricted to the outer centre `X`** (RepH10, copied and adapted). -/
theorem tsum_constWHX_le (X : CentredSlot S → (Fin d → ℤ)) :
    ∑' ξh : A.Xi, ENNReal.ofReal ‖cindX X ξh.1.2 * A.constWH ξh‖ ≤
      (∑' ξ : XiT A.fam, ENNReal.ofReal ‖cindX X ξ.2 * constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖) *
        ∏ j, ENNReal.ofReal (A.Mh j) := by
  have hcnt : ∀ s, Countable (A.fam.Λ s) := A.fam.cnt
  have hsig := ENNReal.tsum_sigma' (β := fun ξ : XiT A.fam => ∀ j, A.H.Λ j (hingeCen A.fam A.hS A.hmom ξ j))
    (fun ξh => ENNReal.ofReal ‖cindX X ξh.1.2 * A.constWH ξh‖)
  refine (le_of_eq hsig).trans ?_
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun ξ => ?_
  have e1 : ∀ ζ : (∀ j, A.H.Λ j (hingeCen A.fam A.hS A.hmom ξ j)),
      ENNReal.ofReal ‖cindX X (⟨ξ, ζ⟩ : A.Xi).1.2 * A.constWH ⟨ξ, ζ⟩‖ =
      ENNReal.ofReal ‖cindX X ξ.2 * constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖ *
        ENNReal.ofReal (∏ j, A.H.w j _ (ζ j)) := by
    intro ζ
    rw [norm_mul, norm_mul, A.norm_constWH, ← mul_assoc, ENNReal.ofReal_mul (by positivity)]
  simp_rw [e1]
  rw [ENNReal.tsum_mul_left]
  gcongr
  rw [tsum_ofReal_prod_fintype (fun j l => A.H.w j (hingeCen A.fam A.hS A.hmom ξ j) l)
    (fun j l => A.H.w_nn j _ l)]
  refine Finset.prod_le_prod' fun j _ => ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (A.H.w_nn j _) (A.H.w_sum j _)]
  exact ENNReal.ofReal_le_ofReal (A.hMh j _)

open scoped Classical in
/-- The restricted slot weights: `‖cindX · constW ξ‖ ≤ Cχ^{#br} · Π w · [ξ.2 ∈ nodeCentreSet] · [ξ.2|centred = X]`. -/
theorem tsum_constWX_le (X : CentredSlot S → (Fin d → ℤ)) :
    ∑' ξ : XiT A.fam, ENNReal.ofReal ‖cindX X ξ.2 * constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖ ≤
      ENNReal.ofReal (A.Cχ ^ (Fintype.card (GBranch S.tree))) *
        ∑' ξ : XiT A.fam, ENNReal.ofReal ((∏ s, A.fam.w s (ξ.1 s)) *
          (if ξ.2 ∈ nodeCentreSet (A.fam.leafCentre A.hS ξ.1) then 1 else 0) * (if ResX X ξ.2 then 1 else 0)) := by
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun ξ => ?_
  rw [← ENNReal.ofReal_mul (pow_nonneg A.hCpos.le _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [norm_cindX_mul]
  have h := norm_constW_le A.fam A.hS A.hd A.Cχ A.hC A.hCpos A.L A.base A.roots A.tt ξ
  have h0 : (0 : ℝ) ≤ (if ResX X ξ.2 then 1 else 0) := by split_ifs <;> norm_num
  calc (if ResX X ξ.2 then (1 : ℝ) else 0) * ‖constW A.fam A.hS A.Cχ A.L A.base A.roots A.tt ξ‖
      ≤ (if ResX X ξ.2 then (1 : ℝ) else 0) * (A.Cχ ^ (Fintype.card (GBranch S.tree)) *
          ((∏ s, A.fam.w s (ξ.1 s)) * (if ξ.2 ∈ nodeCentreSet (A.fam.leafCentre A.hS ξ.1) then 1 else 0))) :=
        mul_le_mul_of_nonneg_left h h0
    _ = _ := by ring

end Dom

open scoped Classical in
/-- **δ's `repIntCMKF_of_asmHD` restricted to the outer centre `X`**: the restricted assembled expansion of the outer
form with the extra decoration weight `chiX X` is a `RepIntCMKF` of the restricted mass. -/
theorem repIntCMKF_of_asmHDX {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (A : AsmCtxH π.Gsb P.d)
    (sel : Finset (GBranch π.Gsb.tree)) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hh : A.hinges = π.Cs.hinges) (hgs : A.gs = π.gapSpecification)
    (hL : A.L = P.L) (hγ : A.γ = P.γ) (hη : A.η = P.η) (hδ : A.δ = P.δ)
    (hbase : A.base = base) (hroots : A.roots = roots) (htt : A.tt = tt)
    (hbox : ∀ τ ∈ domFix π.Gsb π.layer A.tt π.fix π.lb, ∀ s, slotTs A.hS A.tt τ s ∈ A.Box s)
    (hHkD : HkOn A (domFix π.Gsb π.layer A.tt π.fix π.lb))
    (hfilt : ∀ a q, π.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1)
    (X : CentredSlot π.Gsb → (Fin P.d → ℤ))
    (B : ℝ) (hB : 0 ≤ B)
    (hmass : ∑' ξh : A.Xi, ENNReal.ofReal ‖cindX X ξh.1.2 * A.constWH ξh‖ ≤ ENNReal.ofReal B)
    (M : ℝ) (hM : ∀ ξh : A.Xi, momS sel (A.freqH ξh) ≤ M)
    (val : ℂ)
    (hval : val = (coupling P.d A.L A.γ A.δ : ℂ) ^ π.Gsb.order * π.Gsb.zeta *
      ∑' κ : GenDecoration π.Gsb P.d A.roots 0, atomWF π.filt π.ind (cosetDecoration π.Gsb A.L A.base κ.1) *
        ((if A.selSk κ then ((splicedEpsilon π.Gsb A.hinges κ.1 : ℝ) : ℂ) else 0) *
          (chiX A.L A.base X κ * ∫ τ, (domFix π.Gsb π.layer A.tt π.fix π.lb).indicator (fun τ =>
            phaseProd A.L A.γ A.δ π.Gsb (cosetDecoration π.Gsb A.L A.base κ.1) τ * (A.skel κ τ * A.hk κ τ)) τ
            ∂(fixMeasure π.fix)))) :
    RepIntCMKF π sel tt base roots val B M := by
  have hv := value_eqHMDX A π.layer π.fix π.lb hbox hHkD hfilt hind X
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
  have hw_sum : Summable fun ξh : A.Xi => ‖cindX X ξh.1.2 * (π.Gsb.zeta * A.constWH ξh)‖ := by
    have h1 : ∑' ξh : A.Xi, ENNReal.ofReal ‖cindX X ξh.1.2 * A.constWH ξh‖ ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass
    refine (ENNReal.summable_toReal h1).congr fun ξh => ?_
    rw [ENNReal.toReal_ofReal (norm_nonneg _)]
    simp only [norm_mul, norm_zeta, one_mul]
  -- summability of the values (as δ's `repIntCMKF_of_asmHD`)
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
  have hKsX : Summable fun ξh : A.Xi => ‖cindX X ξh.1.2 * (π.Gsb.zeta * A.constWH ξh) *
      splicedKernelMK π.Gsb (DHMKD A π.layer π.fix π.filt π.ind π.lb ξh) A.L A.γ A.η A.δ A.base A.roots‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξh => ?_) hKs
    rw [mul_assoc, norm_mul]
    calc ‖cindX X ξh.1.2‖ * ‖π.Gsb.zeta * A.constWH ξh *
          splicedKernelMK π.Gsb (DHMKD A π.layer π.fix π.filt π.ind π.lb ξh) A.L A.γ A.η A.δ A.base A.roots‖
        ≤ 1 * ‖π.Gsb.zeta * A.constWH ξh *
          splicedKernelMK π.Gsb (DHMKD A π.layer π.fix π.filt π.ind π.lb ξh) A.L A.γ A.η A.δ A.base A.roots‖ :=
          mul_le_mul_of_nonneg_right (norm_cindX_le X _) (norm_nonneg _)
      _ = _ := one_mul _
  refine ⟨A.Xi, inferInstance, fun ξh => cindX X ξh.1.2 * (π.Gsb.zeta * A.constWH ξh),
    fun ξh x => cenS A.fam ξh.1 (slotOfDart A.hS x), fun ξh => edgeS A.fam A.hS A.Cχ ξh.1, hingeT,
    fun ξh => A.freqH ξh, ?_, ?_, hw_sum, ?_, hM, fun ξh => ?_⟩
  · simp_rw [hK]; exact hKsX
  · rw [hv]
    exact tsum_congr fun ξh => by rw [hK]
  · have h1 : ENNReal.ofReal (∑' ξh : A.Xi, ‖cindX X ξh.1.2 * (π.Gsb.zeta * A.constWH ξh)‖) =
        ∑' ξh : A.Xi, ENNReal.ofReal ‖cindX X ξh.1.2 * (π.Gsb.zeta * A.constWH ξh)‖ :=
      ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hw_sum
    have h2 : ∑' ξh : A.Xi, ENNReal.ofReal ‖cindX X ξh.1.2 * (π.Gsb.zeta * A.constWH ξh)‖ ≤ ENNReal.ofReal B := by
      calc _ = ∑' ξh : A.Xi, ENNReal.ofReal ‖cindX X ξh.1.2 * A.constWH ξh‖ :=
            tsum_congr fun ξh => by simp only [norm_mul, norm_zeta, one_mul]
        _ ≤ _ := hmass
    exact (ENNReal.ofReal_le_ofReal_iff hB).1 (h1 ▸ h2)
  · -- amplitude bounds of the transported data
    have hb := A.splicedAmplitudeBounds_DH ξh
    refine ⟨hb.1, hb.2.1, fun K => A.norm_hingeAmp_le ξh _, fun K ⟨x, hx⟩ => ?_⟩
    exact hb.2.2.2 (fun y => K (toP y)) ⟨toA x, hx⟩

end WaveTurbulence.Flower.MkSlotsE
