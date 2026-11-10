/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.PVBR2
public import WaveTurbulence.Foundations.Flower.MkSlots.PVBInteg
public import WaveTurbulence.Foundations.Flower.MkUnitsL.WIntegW
public import WaveTurbulence.Foundations.Flower.MkSlots.OuterFixD

/-! # B3s-HELPER3 B2 (3): the domain-generic VINE-B♯ with unit top weights — definitions, glue, pinned Fubini

Domain-generic copy of `MkSlotsW/PVBW1` (skeleton value), `MkUnitsL/GenW1` (`integrand_glueGW` only) and
`MkUnitsL/GenW2` + `MkSlotsW/PVBW2` (section `Fiber`): the skeleton core domain is an arbitrary set `A` of skeleton
time vectors, the `G_sb` domain an arbitrary set `B` of `G_sb` time vectors (measurable, of pinned mass `≤ 1`); the
only place they interact is the hypothesis `hdom` of the pointwise glue (`integrand_glueGWD`), which replaces main's
`dom_iff`. Instances: `A = coreTimeDomainWR … fixS (∩ lbDomR lbS)`, `B = openSbR … (∩ lbDomR …)` (relaxed, PVBR2);
`A = coreTimeDomainW`, `B = openSb` (MkSlotsW's, by `rfl`).

* `skelTermWD`, `skelValWD`, `modeGWD`, `skelTermWD_eq_integral`; **`skelValWFR`** (relaxed core domain),
  **`skelValWFRL`** (with lower bounds), `skelValWFRL_lbnone`, `skelValWFR_none`, `skelValWD_coreTimeDomainW`;
* `psiIntGWD`, `fibIntGWD`, `boxQD` and their measurability/bounds, `inner_psiIntGWD`, `integral_psiIntGWD_fix`,
  `integrable_fibIntGWD_fix`, `fiber_sumGWD_fix`;
* **`integrand_glueGWD`**: the pointwise factorization on the domains `A`, `B`. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract

namespace WaveTurbulence.Flower.MkSlotsB
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB
open WaveTurbulence.Flower.MkSlots (fixMeasure fixMeasure_none integrable_indicator_const_of_le_one
  integral_indicator_const_le_of_le_one)
open WaveTurbulence.Flower.MkUnitsL (SlotFamW RegBoundW topW unitIntGW unitIGW modalFnGW gUnitGW clLocalSummandGW
  measurable_unitIntGW norm_gUnitG_leW norm_unitIG_leW summable_unitIGW prod_modalFnG_topW regional_glueGW
  skelValW skelValW_eq)

/-! ## The skeleton value on a core domain `A` -/

section Skel

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J]

open scoped Classical in
/-- The summand of the skeleton value on the core domain `A` (`MkSlotsW.skelTermWF` with `A` in place of
`coreTimeDomainW`). -/
def skelTermWD (blk : J → CLBlock S) (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop) (Fs : SlotFamW S d)
    (A : Set (GBranch S.tree → ℝ)) (fixS : GBranch S.tree → Option ℝ) (κ : GenDecoration S d roots 0) : ℂ :=
  if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
      A.indicator (fun τ => phaseProd L γ δ S (cosetDecoration S L base κ.1) τ *
          ((∏ s, Fs.fs s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s)))) *
            topW blk Fs L base κ.1)) τ ∂(fixMeasure fixS) else 0

/-- The pinned skeleton value on the core domain `A`. -/
def skelValWD (blk : J → CLBlock S) (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop) (Fs : SlotFamW S d)
    (A : Set (GBranch S.tree → ℝ)) (fixS : GBranch S.tree → Option ℝ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
    ∑' κ : GenDecoration S d roots 0, skelTermWD blk hS L γ δ base roots tt selSk Fs A fixS κ

/-- The skeleton integrand on the core domain `A`. -/
def modeGWD (blk : J → CLBlock S) (Fs : SlotFamW S d) (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (A : Set (GBranch S.tree → ℝ)) (κ : GenDecoration S d roots 0)
    (τ : GBranch S.tree → ℝ) : ℂ :=
  (epsDec S κ.1 : ℂ) * A.indicator
    (fun τ => phaseProd L γ δ S (cosetDecoration S L base κ.1) τ *
      ((∏ s, Fs.fs s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s)))) *
        topW blk Fs L base κ.1)) τ

open scoped Classical in
theorem skelTermWD_eq_integral (blk : J → CLBlock S) (Fs : SlotFamW S d) (hS : S.IsPlain) (L γ δ : ℝ)
    (base : Mom d) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop)
    (A : Set (GBranch S.tree → ℝ)) (fixS : GBranch S.tree → Option ℝ) (κ : GenDecoration S d roots 0) :
    skelTermWD blk hS L γ δ base roots tt selSk Fs A fixS κ =
      if selSk κ then ∫ τ, modeGWD blk Fs hS L γ δ base tt A κ τ ∂(fixMeasure fixS) else 0 := by
  unfold skelTermWD modeGWD
  split_ifs
  · rw [integral_const_mul]
  · rfl

end Skel

/-! ## The `G_sb` integrands on a domain `B` -/

section Fiber

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb)

/-- The product integrand of the glued integral on the `G_sb` domain `B` (`MkUnitsL.psiIntGW` with `B`). -/
def psiIntGWD (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (L γ δ : ℝ) (base : Mom d) (Fs : SlotFamW S d)
    (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (B : Set (GBranch Gsb.tree → ℝ))
    (p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j)))) : ℂ :=
  (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
    B.indicator (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
        ∏ j, unitIntGW Φ D hS Fs L γ δ layer base frq hSb z τ' j (κs j) (p.2 j)) p.1

/-- The fiber integrand over `G_sb` times on the domain `B` (`MkUnitsL.fibIntGW` with `B`). -/
def fibIntGWD (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (L γ δ : ℝ) (base : Mom d) (Fs : SlotFamW S d)
    (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (B : Set (GBranch Gsb.tree → ℝ)) (τ' : GBranch Gsb.tree → ℝ) : ℂ :=
  (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
    B.indicator (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
        ∏ j, (Φ.recJ L γ δ base z τ' j * unitIGW Φ D hS hSb L γ δ Fs layer base frq z τ' j (κs j))) τ'

/-- The domain `B` times the unit boxes. -/
def boxQD (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (B : Set (GBranch Gsb.tree → ℝ)) : Set ((GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j)))) :=
  B ×ˢ Set.pi Set.univ (fun j => boxU D hS layer blk j)

theorem measurableSet_boxQD (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    {B : Set (GBranch Gsb.tree → ℝ)} (hB : MeasurableSet B) : MeasurableSet (boxQD (blk := blk) D hS layer B) := by
  unfold boxQD boxU
  exact hB.prod (MeasurableSet.univ_pi fun j => MeasurableSet.univ_pi fun _ => measurableSet_Icc)

theorem fixMeasure_boxQD_le (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    {B : Set (GBranch Gsb.tree → ℝ)} (fixSb : GBranch Gsb.tree → Option ℝ) (hBμ : fixMeasure fixSb B ≤ 1) :
    ((fixMeasure fixSb).prod (volume : Measure (∀ j, CLInternalTime (regionOf (blk j)))))
      (boxQD (blk := blk) D hS layer B) ≤ 1 := by
  unfold boxQD
  rw [Measure.prod_prod, volume_pi_pi]
  simp only [volume_boxU, Finset.prod_const_one, mul_one]
  exact hBμ

variable {hS : S.IsPlain} {Fs : SlotFamW S d} {L : ℝ} {base : Mom d}

theorem measurable_psiIntGWD (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    {B : Set (GBranch Gsb.tree → ℝ)} (hB : MeasurableSet B) :
    Measurable (psiIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B) := by
  have hg : Measurable fun p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))) =>
      Φ.sbInt hS hSb L γ δ base tt amp frq z p.1 *
        ∏ j, unitIntGW Φ D hS Fs L γ δ layer base frq hSb z p.1 j (κs j) (p.2 j) :=
    ((Φ.measurable_sbInt hS hSb L γ δ base tt amp frq z).comp measurable_fst).mul
      (Finset.measurable_prod _ fun j _ =>
        measurable_unitIntGW Φ D hS Fs L γ δ layer base frq hSb z j (RB.meas j) (κs j))
  have hO : MeasurableSet (Prod.fst ⁻¹' B :
      Set ((GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))))) := hB.preimage measurable_fst
  have : psiIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B = fun p =>
      (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) * (Prod.fst ⁻¹' B).indicator
        (fun p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))) =>
          Φ.sbInt hS hSb L γ δ base tt amp frq z p.1 *
          ∏ j, unitIntGW Φ D hS Fs L γ δ layer base frq hSb z p.1 j (κs j) (p.2 j)) p := by
    funext p
    unfold psiIntGWD
    simp only [Set.indicator, Set.mem_preimage]
    rfl
  rw [this]
  exact measurable_const.mul (hg.indicator hO)

theorem norm_psiIntGWD_le (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (B : Set (GBranch Gsb.tree → ℝ))
    (p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j)))) :
    ‖psiIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B p‖ ≤
      (boxQD (blk := blk) D hS layer B).indicator
        (fun _ => ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1)) p := by
  have hU : ∏ j, ‖unitIntGW Φ D hS Fs L γ δ layer base frq hSb z p.1 j (κs j) (p.2 j)‖ ≤
      (Set.pi Set.univ fun j => boxU D hS layer blk j).indicator
        (fun _ => ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1)) p.2 := by
    have hj : ∀ j, ‖unitIntGW Φ D hS Fs L γ δ layer base frq hSb z p.1 j (κs j) (p.2 j)‖ ≤
        (boxU D hS layer blk j).indicator
          (fun _ => RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1)) (p.2 j) := fun j => by
      unfold unitIntGW
      rw [norm_mul, norm_recExp, one_mul]
      exact norm_gUnitG_leW RB D γ δ layer j _ _ _ (κs j) (p.2 j)
    by_cases hpi : p.2 ∈ Set.pi Set.univ fun j => boxU D hS layer blk j
    · rw [Set.indicator_of_mem hpi]
      refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => ?_
      have := hj j
      rwa [Set.indicator_of_mem (hpi j (Set.mem_univ j))] at this
    · rw [Set.indicator_of_notMem hpi]
      obtain ⟨j, hjn⟩ : ∃ j, p.2 j ∉ boxU D hS layer blk j := by
        by_contra hc
        push Not at hc
        exact hpi fun j _ => hc j
      have h0 : ‖unitIntGW Φ D hS Fs L γ δ layer base frq hSb z p.1 j (κs j) (p.2 j)‖ = 0 := by
        have := hj j
        rw [Set.indicator_of_notMem hjn] at this
        exact le_antisymm this (norm_nonneg _)
      rw [Finset.prod_eq_zero (Finset.mem_univ j) h0]
  have hlb0 : 0 ≤ ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) :=
    mul_nonneg (ampBound_nonneg _ _ _ _ _) (Finset.prod_nonneg fun j _ => RB.nonneg j _)
  unfold psiIntGWD
  by_cases hp : p.1 ∈ B
  · rw [Set.indicator_of_mem hp]
    have h1 : ‖(splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_splicedEpsilon_le _ _ _
    have h2 : ‖Φ.sbInt hS hSb L γ δ base tt amp frq z p.1‖ ≤ ampBound hSb L base amp z := by
      unfold SpliceShape.sbInt ampBound
      rw [norm_mul, norm_mul, norm_phaseProd_le, norm_routedPhase, norm_prod]
      simp
    have hb : ‖(splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) * (Φ.sbInt hS hSb L γ δ base tt amp frq z p.1 *
        ∏ j, unitIntGW Φ D hS Fs L γ δ layer base frq hSb z p.1 j (κs j) (p.2 j))‖ ≤
        ampBound hSb L base amp z * ((Set.pi Set.univ fun j => boxU D hS layer blk j).indicator
          (fun _ => ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1)) p.2) := by
      rw [norm_mul, norm_mul, norm_prod]
      calc _ ≤ 1 * (ampBound hSb L base amp z * ((Set.pi Set.univ fun j => boxU D hS layer blk j).indicator
          (fun _ => ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1)) p.2)) :=
            mul_le_mul h1 (mul_le_mul h2 hU (Finset.prod_nonneg fun _ _ => norm_nonneg _)
              (ampBound_nonneg _ _ _ _ _)) (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
              zero_le_one
        _ = _ := one_mul _
    by_cases hpi : p.2 ∈ Set.pi Set.univ fun j => boxU D hS layer blk j
    · have hq : p ∈ boxQD (blk := blk) D hS layer B := ⟨hp, hpi⟩
      rw [Set.indicator_of_mem hq]
      rwa [Set.indicator_of_mem hpi] at hb
    · rw [Set.indicator_of_notMem hpi, mul_zero] at hb
      exact hb.trans (Set.indicator_nonneg (fun _ _ => hlb0) _)
  · rw [Set.indicator_of_notMem hp]
    simp only [mul_zero, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hlb0) _

theorem integrable_psiIntGWD_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (fixSb : GBranch Gsb.tree → Option ℝ) {B : Set (GBranch Gsb.tree → ℝ)} (hB : MeasurableSet B)
    (hBμ : fixMeasure fixSb B ≤ 1) :
    Integrable (psiIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B)
      ((fixMeasure fixSb).prod (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) := by
  have hg := integrable_indicator_const_of_le_one (measurableSet_boxQD (blk := blk) D hS layer hB)
    (fixMeasure_boxQD_le (blk := blk) D hS layer fixSb hBμ)
    (ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1))
  exact hg.mono' (measurable_psiIntGWD Φ RB hd D hSb γ δ layer tt amp frq z κs hB).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => norm_psiIntGWD_le Φ RB hd D hSb γ δ layer tt amp frq z κs B p)

theorem norm_integral_psiIntGWD_le_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk)
    (D : ReconstructionData S) (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (fixSb : GBranch Gsb.tree → Option ℝ) {B : Set (GBranch Gsb.tree → ℝ)} (hB : MeasurableSet B)
    (hBμ : fixMeasure fixSb B ≤ 1) :
    ‖∫ p, psiIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B p
        ∂((fixMeasure fixSb).prod (volume : Measure (∀ j, CLInternalTime (regionOf (blk j)))))‖ ≤
      ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) := by
  refine (norm_integral_le_integral_norm _).trans ?_
  have hQ := measurableSet_boxQD (blk := blk) D hS layer hB
  have h1 := fixMeasure_boxQD_le (blk := blk) D hS layer fixSb hBμ
  have hc : 0 ≤ ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) :=
    mul_nonneg (ampBound_nonneg _ _ _ _ _) (Finset.prod_nonneg fun j _ => RB.nonneg j _)
  refine (integral_mono (integrable_psiIntGWD_fix Φ RB hd D hSb γ δ layer tt amp frq z κs fixSb hB hBμ).norm
    (integrable_indicator_const_of_le_one hQ h1 _)
    fun p => norm_psiIntGWD_le Φ RB hd D hSb γ δ layer tt amp frq z κs B p).trans ?_
  exact integral_indicator_const_le_of_le_one hQ h1 hc

theorem inner_psiIntGWD (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (B : Set (GBranch Gsb.tree → ℝ)) (τ' : GBranch Gsb.tree → ℝ) :
    ∫ τs : (∀ j, CLInternalTime (regionOf (blk j))),
      psiIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B (τ', τs) =
    fibIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B τ' := by
  unfold psiIntGWD fibIntGWD
  by_cases hp : τ' ∈ B
  · simp only [Set.indicator_of_mem hp]
    rw [integral_const_mul, integral_const_mul]
    congr 2
    have := integral_fintype_prod_volume_eq_prod (𝕜 := ℂ) (ι := J)
      (E := fun j => CLInternalTime (regionOf (blk j)))
      (fun j (τ : CLInternalTime (regionOf (blk j))) =>
        unitIntGW Φ D hS Fs L γ δ layer base frq hSb z τ' j (κs j) τ)
    rw [this]
    refine Finset.prod_congr rfl fun j _ => ?_
    unfold unitIntGW SpliceShape.recJ unitIGW
    rw [integral_const_mul]
  · simp only [Set.indicator_of_notMem hp]
    simp

theorem integral_psiIntGWD_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (fixSb : GBranch Gsb.tree → Option ℝ) {B : Set (GBranch Gsb.tree → ℝ)} (hB : MeasurableSet B)
    (hBμ : fixMeasure fixSb B ≤ 1) :
    ∫ p, psiIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B p
        ∂((fixMeasure fixSb).prod (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) =
      ∫ τ', fibIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B τ' ∂(fixMeasure fixSb) := by
  rw [integral_prod _ (integrable_psiIntGWD_fix Φ RB hd D hSb γ δ layer tt amp frq z κs fixSb hB hBμ)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun τ' =>
    inner_psiIntGWD Φ hd D hSb γ δ layer tt amp frq z κs B τ')

theorem integrable_fibIntGWD_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (fixSb : GBranch Gsb.tree → Option ℝ) {B : Set (GBranch Gsb.tree → ℝ)} (hB : MeasurableSet B)
    (hBμ : fixMeasure fixSb B ≤ 1) :
    Integrable (fibIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B) (fixMeasure fixSb) := by
  have := (integrable_psiIntGWD_fix Φ RB hd D hSb γ δ layer tt amp frq z κs fixSb hB hBμ).integral_prod_left
  have hfun : (fun τ' => ∫ τs : (∀ j, CLInternalTime (regionOf (blk j))),
      psiIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B (τ', τs)) =
      fibIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B :=
    funext fun τ' => inner_psiIntGWD Φ hd D hSb γ δ layer tt amp frq z κs B τ'
  rwa [hfun] at this

theorem norm_fibIntGWD_le (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (B : Set (GBranch Gsb.tree → ℝ)) (τ' : GBranch Gsb.tree → ℝ) :
    ‖fibIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B τ'‖ ≤
      B.indicator
        (fun _ => ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1)) τ' := by
  have hlb0 : 0 ≤ ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) :=
    mul_nonneg (ampBound_nonneg _ _ _ _ _) (Finset.prod_nonneg fun j _ => RB.nonneg j _)
  unfold fibIntGWD
  by_cases hp : τ' ∈ B
  · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    have h1 : ‖(splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_splicedEpsilon_le _ _ _
    have h2 : ‖Φ.sbInt hS hSb L γ δ base tt amp frq z τ'‖ ≤ ampBound hSb L base amp z := by
      unfold SpliceShape.sbInt ampBound
      rw [norm_mul, norm_mul, norm_phaseProd_le, norm_routedPhase, norm_prod]
      simp
    have h3 : ∏ j, ‖Φ.recJ L γ δ base z τ' j * unitIGW Φ D hS hSb L γ δ Fs layer base frq z τ' j (κs j)‖ ≤
        ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) := by
      refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => ?_
      rw [norm_mul, Φ.norm_recJ, one_mul]
      exact norm_unitIG_leW Φ RB D hSb γ δ layer frq z τ' j (κs j)
    rw [norm_mul, norm_mul, norm_prod]
    calc _ ≤ 1 * (ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1)) :=
          mul_le_mul h1 (mul_le_mul h2 h3 (Finset.prod_nonneg fun _ _ => norm_nonneg _)
            (ampBound_nonneg _ _ _ _ _)) (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
            zero_le_one
      _ = _ := one_mul _
  · rw [Set.indicator_of_notMem hp]
    simp only [mul_zero, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hlb0) _

theorem fiber_sumGWD_fix (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0) (fixSb : GBranch Gsb.tree → Option ℝ) {B : Set (GBranch Gsb.tree → ℝ)}
    (hB : MeasurableSet B) (hBμ : fixMeasure fixSb B ≤ 1) :
    ∑' κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)),
      ∫ p, psiIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B p
        ∂((fixMeasure fixSb).prod (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) =
    ∫ τ' : GBranch Gsb.tree → ℝ, (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
      B.indicator
        (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
          ∏ j, (Φ.recJ L γ δ base z τ' j *
            ∑' κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j),
              unitIGW Φ D hS hSb L γ δ Fs layer base frq z τ' j κ)) τ' ∂(fixMeasure fixSb) := by
  have hK : Summable fun κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
      ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) :=
    ((summable_pi_prod_dep (fun j (κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
      RB.lb j (clExtendIndices (regionOf (blk j)) κ.1))
      (fun j κ => RB.nonneg j _) (fun j => RB.summable j _)).1).mul_left _
  have hsum : Summable fun κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
      ∫ τ', ‖fibIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B τ'‖ ∂(fixMeasure fixSb) := by
    refine Summable.of_nonneg_of_le (fun κs => integral_nonneg fun _ => norm_nonneg _) (fun κs => ?_) hK
    have hc : 0 ≤ ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) :=
      mul_nonneg (ampBound_nonneg _ _ _ _ _) (Finset.prod_nonneg fun j _ => RB.nonneg j _)
    refine (integral_mono (integrable_fibIntGWD_fix Φ RB hd D hSb γ δ layer tt amp frq z κs fixSb hB hBμ).norm
      (integrable_indicator_const_of_le_one hB hBμ _)
      fun τ' => norm_fibIntGWD_le Φ RB hd D hSb γ δ layer tt amp frq z κs B τ').trans ?_
    exact integral_indicator_const_le_of_le_one hB hBμ hc
  simp_rw [integral_psiIntGWD_fix Φ RB hd D hSb γ δ layer tt amp frq z _ fixSb hB hBμ]
  rw [integral_tsum_of_summable_integral_norm
    (fun κs => integrable_fibIntGWD_fix Φ RB hd D hSb γ δ layer tt amp frq z κs fixSb hB hBμ) hsum]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ' => ?_)
  by_cases hp : τ' ∈ B
  · unfold fibIntGWD
    simp only [Set.indicator_of_mem hp]
    rw [tsum_mul_left, tsum_mul_left]
    congr 2
    have hs : ∀ j, Summable fun κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j) =>
        Φ.recJ L γ δ base z τ' j * unitIGW Φ D hS hSb L γ δ Fs layer base frq z τ' j κ :=
      fun j => (summable_unitIGW Φ RB D hSb γ δ layer frq z τ' j).mul_left _
    rw [tsum_pi_prod_complex (fun j κ => Φ.recJ L γ δ base z τ' j *
      unitIGW Φ D hS hSb L γ δ Fs layer base frq z τ' j κ) hs]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [tsum_mul_left]
  · unfold fibIntGWD
    simp [Set.indicator_of_notMem hp]

end Fiber

/-! ## The pointwise glue on the domains `A`, `B` -/

section Glued

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb)

/-- **The pointwise factorization on general domains** (`MkUnitsL.integrand_glueGW` with the domain split `hdom` at
`(τ', τs)` in place of main's `dom_iff`). -/
theorem integrand_glueGWD (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain) {L : ℝ}
    (hL : L ≠ 0) (γ δ : ℝ) (base : Mom d) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    (Fs : SlotFamW S d) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (A : Set (GBranch S.tree → ℝ)) (B : Set (GBranch Gsb.tree → ℝ))
    (τ' : GBranch Gsb.tree → ℝ) (τs : ∀ j, CLInternalTime (regionOf (blk j)))
    (hdom : Φ.glueTime hd τ' τs ∈ A ↔ τ' ∈ B ∧
      ∀ j, τs j ∈ clLocalTimeDomain (regionOf (blk j)) (fun b => layer (D.coreBranch hS b).toNode) (Φ.clocks τ' j)) :
    modeGWD blk (modalFnGW Φ hS hSb Fs amp frq) hS L γ δ base tt A (Φ.glueDec hS hd hL base z κs)
        (Φ.glueTime hd τ' τs) =
      psiIntGWD Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs B (τ', τs) := by
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = Φ.glueDec hS hd hL base z κs := ⟨_, rfl⟩
  unfold modeGWD psiIntGWD
  dsimp only
  rw [← hκ]
  by_cases hτ : Φ.glueTime hd τ' τs ∈ A
  · obtain ⟨hsb, hloc⟩ := hdom.mp hτ
    rw [Set.indicator_of_mem hτ, Set.indicator_of_mem hsb]
    have hκv : κ.1 = Φ.glueFun z.1 (fun j => (κs j).1) := by rw [hκ]; exact Φ.glueDec_val hS hd hL base z κs
    rw [hκv]
    rw [prod_modalFnG_topW Φ hd hS hSb Fs amp frq tt (Φ.glueTime hd τ' τs)
      (fun x => base + latticePoint L (Φ.glueFun z.1 (fun j => (κs j).1) x)) L base
      (Φ.glueFun z.1 (fun j => (κs j).1))]
    rw [Φ.amp_glue hS hSb L base z.1 (fun j => (κs j).1) amp, Φ.modes_glue hd hS hSb tt frq τ' τs]
    have hreg := Finset.prod_congr (s₁ := (Finset.univ : Finset J)) rfl
      (fun j _ => regional_glueGW Φ hd hS hL base Fs tt z κs τ' τs j)
    rw [hreg]
    rw [Φ.eps_glue hd hL base z κs, Φ.phase_glue hd hL γ δ base z κs τ' τs]
    unfold SpliceShape.sbInt unitIntGW gUnitGW clLocalSummandGW
    simp only [Set.indicator_of_mem (hloc _), Finset.prod_mul_distrib, Complex.ofReal_mul, Complex.ofReal_prod]
    ring
  · rw [Set.indicator_of_notMem hτ, mul_zero]
    rw [hdom.not] at hτ
    by_cases hsb : τ' ∈ B
    · have : ∃ j, τs j ∉ clLocalTimeDomain (regionOf (blk j)) (fun b => layer (D.coreBranch hS b).toNode)
          (Φ.clocks τ' j) := by
        by_contra hc
        push Not at hc
        exact hτ ⟨hsb, hc⟩
      obtain ⟨j, hj⟩ := this
      rw [Set.indicator_of_mem hsb]
      have h0 : unitIntGW Φ D hS Fs L γ δ layer base frq hSb z τ' j (κs j) (τs j) = 0 := by
        unfold unitIntGW gUnitGW clLocalSummandGW
        rw [Set.indicator_of_notMem hj]
        simp
      rw [Finset.prod_eq_zero (Finset.mem_univ j) h0]
      simp
    · rw [Set.indicator_of_notMem hsb]
      simp

end Glued

end WaveTurbulence.Flower.MkSlotsB
