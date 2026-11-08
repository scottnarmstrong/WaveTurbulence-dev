/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.GenVB1

/-! # STAGE1W-VINE (T3): VINE-B♯ with an arbitrary regional slot family — bounds and Fubini

Copy-generalization of `Vine/B/{Unit, Fiber1–6}` from the native kernels to an arbitrary slot family `Fs`, under the
abstract regional bound `RegBound` (a pointwise bound of the regional star product by a function `lb j` of the local
decoration, summable over the local decorations of every boundary datum, and measurability of `Fs` in the clocks).
For the native kernels `RegBound` is V5's `localBound` (`summable_tsum_localBound`); for the frontier-weighted kernels
it is `cψ`-powers times the same (row file `WRow*`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.Stage1WVine
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

/-- **The abstract regional bound** of a slot family on the units `blk`. -/
structure RegBound (blk : J → CLBlock S) (hS : S.IsPlain) (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ)
    (L : ℝ) (base : Mom d) where
  lb : J → (GNode S.tree → (Fin d → ℤ)) → ℝ
  lbC : J → ℝ
  nonneg : ∀ j x, 0 ≤ lb j x
  norm_le : ∀ j x top u, ‖starProdG hS Fs L base (blk j).atoms (blk j).upper top x u‖ ≤ lb j x
  summable : ∀ j (β : Fin 4 → Mom d), Summable fun κ : CLLocalDecoration (regionOf (blk j)) L base β =>
    lb j (clExtendIndices (regionOf (blk j)) κ.1)
  tsum_le : ∀ j (β : Fin 4 → Mom d), ∑' κ : CLLocalDecoration (regionOf (blk j)) L base β,
    lb j (clExtendIndices (regionOf (blk j)) κ.1) ≤ lbC j
  meas : ∀ j, RegMeas hS Fs L base (blk j).atoms (blk j).upper

section UnitBounds
variable {hS : S.IsPlain} {Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ} {L : ℝ} {base : Mom d}

theorem lbC_nonneg (RB : RegBound blk hS Fs L base) (j : J) (β : Fin 4 → Mom d) : 0 ≤ RB.lbC j :=
  (tsum_nonneg fun κ => RB.nonneg j _).trans (RB.tsum_le j β)

theorem norm_clLocalSummandG_le (RB : RegBound blk hS Fs L base) (D : ReconstructionData S)
    (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) (j : J) (β : Fin 4 → Mom d) (t : Fin 3 → ℝ)
    (κ : CLLocalDecoration (regionOf (blk j)) L base β) (τ : CLInternalTime (regionOf (blk j))) :
    ‖clLocalSummandG D hS (regionOf (blk j)) Fs L γ δ layer base β t κ τ‖ ≤
      (boxU D hS layer blk j).indicator (fun _ => RB.lb j (clExtendIndices (regionOf (blk j)) κ.1)) τ := by
  classical
  unfold clLocalSummandG
  by_cases hτ : τ ∈ clLocalTimeDomain (regionOf (blk j)) (fun v => layer (D.coreBranch hS v).toNode) t
  · have hbox : τ ∈ boxU D hS layer blk j := localTimeDomain_subset_box (regionOf (blk j)) _ t hτ
    rw [Set.indicator_of_mem hτ, Set.indicator_of_mem hbox, norm_mul, norm_mul, norm_clRegionalPhase, one_mul]
    calc _ ≤ 1 * RB.lb j (clExtendIndices (regionOf (blk j)) κ.1) :=
          mul_le_mul (norm_clRegionalEpsilon_le _ _) (RB.norm_le j _ _ _) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · rw [Set.indicator_of_notMem hτ, mul_zero, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => RB.nonneg j _) _

theorem norm_gUnitG_le (RB : RegBound blk hS Fs L base) (D : ReconstructionData S)
    (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) (j : J) (lam : ℝ) (β : Fin 4 → Mom d) (t : Fin 3 → ℝ)
    (κ : CLLocalDecoration (regionOf (blk j)) L base β) (τ : CLInternalTime (regionOf (blk j))) :
    ‖gUnitG blk D hS Fs L γ δ layer base j lam β t κ τ‖ ≤
      (boxU D hS layer blk j).indicator (fun _ => RB.lb j (clExtendIndices (regionOf (blk j)) κ.1)) τ := by
  unfold gUnitG
  rw [norm_mul, norm_lowModC, one_mul]
  exact norm_clLocalSummandG_le RB D γ δ layer j β t κ τ

theorem measurable_gUnitG (RB : RegBound blk hS Fs L base) (D : ReconstructionData S)
    (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) (j : J) (lam : ℝ) (β : Fin 4 → Mom d) (t : Fin 3 → ℝ)
    (κ : CLLocalDecoration (regionOf (blk j)) L base β) :
    Measurable fun τ : CLInternalTime (regionOf (blk j)) => gUnitG blk D hS Fs L γ δ layer base j lam β t κ τ := by
  have ht : ∀ i, Measurable fun _ : CLInternalTime (regionOf (blk j)) => t i := fun i => measurable_const
  have hτ : ∀ v, Measurable fun τ : CLInternalTime (regionOf (blk j)) => τ v := fun v => measurable_pi_apply v
  have h1 := measurable_clLocalSummandG_joint D hS (regionOf (blk j)) Fs L γ δ base (RB.meas j) layer β κ
    (fun _ : CLInternalTime (regionOf (blk j)) => t) (fun τ => τ) ht hτ
  have hm : Measurable fun τ : CLInternalTime (regionOf (blk j)) => lowModC (regionOf (blk j)) lam t τ := by
    have hb := measurable_clLocalClock_joint (regionOf (blk j)) (fun _ : CLInternalTime (regionOf (blk j)) => t)
      (fun τ => τ) ht hτ (blk j).lower
    unfold lowModC
    exact Measurable.cexp ((Complex.measurable_ofReal.comp (hb.const_mul (Real.pi * lam))).mul_const Complex.I)
  exact hm.mul h1

theorem integrable_gUnitG (RB : RegBound blk hS Fs L base) (D : ReconstructionData S)
    (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) (j : J) (lam : ℝ) (β : Fin 4 → Mom d) (t : Fin 3 → ℝ)
    (κ : CLLocalDecoration (regionOf (blk j)) L base β) :
    Integrable fun τ : CLInternalTime (regionOf (blk j)) => gUnitG blk D hS Fs L γ δ layer base j lam β t κ τ := by
  have hB : MeasurableSet (boxU D hS layer blk j) := by
    unfold boxU
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hg : Integrable ((boxU D hS layer blk j).indicator
      (fun _ => RB.lb j (clExtendIndices (regionOf (blk j)) κ.1))) :=
    (integrable_indicator_iff hB).2 (integrableOn_const (by rw [volume_boxU]; exact ENNReal.one_ne_top))
  exact hg.mono' (measurable_gUnitG RB D γ δ layer j lam β t κ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun τ => norm_gUnitG_le RB D γ δ layer j lam β t κ τ)

theorem norm_integral_gUnitG_le (RB : RegBound blk hS Fs L base) (D : ReconstructionData S)
    (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) (j : J) (lam : ℝ) (β : Fin 4 → Mom d) (t : Fin 3 → ℝ)
    (κ : CLLocalDecoration (regionOf (blk j)) L base β) :
    ‖∫ τ : CLInternalTime (regionOf (blk j)), gUnitG blk D hS Fs L γ δ layer base j lam β t κ τ‖ ≤
      RB.lb j (clExtendIndices (regionOf (blk j)) κ.1) := by
  have hB : MeasurableSet (boxU D hS layer blk j) := by
    unfold boxU
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hg : Integrable ((boxU D hS layer blk j).indicator
      (fun _ => RB.lb j (clExtendIndices (regionOf (blk j)) κ.1))) :=
    (integrable_indicator_iff hB).2 (integrableOn_const (by rw [volume_boxU]; exact ENNReal.one_ne_top))
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_mono (integrable_gUnitG RB D γ δ layer j lam β t κ).norm hg
    fun τ => norm_gUnitG_le RB D γ δ layer j lam β t κ τ).trans_eq ?_
  rw [integral_indicator_const _ hB, Measure.real, volume_boxU]
  simp

end UnitBounds

section Fiber
variable (Φ : SpliceShape blk Gsb)

/-- The product integrand of the glued integral (`VineB.SpliceShape.psiInt` with `Fs`). -/
def psiIntG (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (L γ δ : ℝ) (base : Mom d) (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j)))) : ℂ :=
  (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
    (openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt).indicator
      (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
        ∏ j, unitIntG Φ D hS Fs L γ δ layer base frq hSb z τ' j (κs j) (p.2 j)) p.1

variable {hS : S.IsPlain} {Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ} {L : ℝ} {base : Mom d}

theorem measurable_psiIntG (RB : RegBound blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    Measurable (psiIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs) := by
  have hg : Measurable fun p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))) =>
      Φ.sbInt hS hSb L γ δ base tt amp frq z p.1 *
        ∏ j, unitIntG Φ D hS Fs L γ δ layer base frq hSb z p.1 j (κs j) (p.2 j) :=
    ((Φ.measurable_sbInt hS hSb L γ δ base tt amp frq z).comp measurable_fst).mul
      (Finset.measurable_prod _ fun j _ => measurable_unitIntG Φ D hS Fs L γ δ layer base frq hSb z j (RB.meas j) (κs j))
  have hO : MeasurableSet (Prod.fst ⁻¹' openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt :
      Set ((GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))))) :=
    (measurableSet_openSb _ _ _).preimage measurable_fst
  have : psiIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs = fun p =>
      (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) * (Prod.fst ⁻¹' openSb Gsb
        (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt).indicator
        (fun p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))) =>
          Φ.sbInt hS hSb L γ δ base tt amp frq z p.1 *
          ∏ j, unitIntG Φ D hS Fs L γ δ layer base frq hSb z p.1 j (κs j) (p.2 j)) p := by
    funext p
    unfold psiIntG
    simp only [Set.indicator, Set.mem_preimage]
    congr
  rw [this]
  exact measurable_const.mul (hg.indicator hO)

theorem norm_psiIntG_le (RB : RegBound blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j)))) :
    ‖psiIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs p‖ ≤
      (SpliceShape.boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)).indicator
        (fun _ => ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1)) p := by
  have hU : ∏ j, ‖unitIntG Φ D hS Fs L γ δ layer base frq hSb z p.1 j (κs j) (p.2 j)‖ ≤
      (Set.pi Set.univ fun j => boxU D hS layer blk j).indicator
        (fun _ => ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1)) p.2 := by
    have hj : ∀ j, ‖unitIntG Φ D hS Fs L γ δ layer base frq hSb z p.1 j (κs j) (p.2 j)‖ ≤
        (boxU D hS layer blk j).indicator
          (fun _ => RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1)) (p.2 j) := fun j => by
      unfold unitIntG
      rw [norm_mul, norm_recExp, one_mul]
      exact norm_gUnitG_le RB D γ δ layer j _ _ _ (κs j) (p.2 j)
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
      have h0 : ‖unitIntG Φ D hS Fs L γ δ layer base frq hSb z p.1 j (κs j) (p.2 j)‖ = 0 := by
        have := hj j
        rw [Set.indicator_of_notMem hjn] at this
        exact le_antisymm this (norm_nonneg _)
      rw [Finset.prod_eq_zero (Finset.mem_univ j) h0]
  have hlb0 : 0 ≤ ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) :=
    mul_nonneg (ampBound_nonneg _ _ _ _ _) (Finset.prod_nonneg fun j _ => RB.nonneg j _)
  unfold psiIntG
  by_cases hp : p.1 ∈ openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt
  · rw [Set.indicator_of_mem hp]
    have h1 : ‖(splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_splicedEpsilon_le _ _ _
    have h2 : ‖Φ.sbInt hS hSb L γ δ base tt amp frq z p.1‖ ≤ ampBound hSb L base amp z := by
      unfold SpliceShape.sbInt ampBound
      rw [norm_mul, norm_mul, norm_phaseProd_le, norm_routedPhase, norm_prod]
      simp
    have hb : ‖(splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) * (Φ.sbInt hS hSb L γ δ base tt amp frq z p.1 *
        ∏ j, unitIntG Φ D hS Fs L γ δ layer base frq hSb z p.1 j (κs j) (p.2 j))‖ ≤
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
    · have hq : p ∈ SpliceShape.boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) :=
        ⟨openSb_subset_box _ _ hp, hpi⟩
      rw [Set.indicator_of_mem hq]
      rwa [Set.indicator_of_mem hpi] at hb
    · rw [Set.indicator_of_notMem hpi, mul_zero] at hb
      exact hb.trans (Set.indicator_nonneg (fun _ _ => hlb0) _)
  · rw [Set.indicator_of_notMem hp]
    simp only [mul_zero, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hlb0) _

theorem integrable_psiIntG (RB : RegBound blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    Integrable (psiIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs)
      ((volume : Measure (GBranch Gsb.tree → ℝ)).prod
        (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) := by
  have hQ := SpliceShape.measurableSet_boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
  have hv := SpliceShape.volume_boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
  have hg : Integrable ((SpliceShape.boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)).indicator
      (fun _ => ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1)))
      ((volume : Measure (GBranch Gsb.tree → ℝ)).prod
        (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) :=
    (integrable_indicator_iff hQ).2 (integrableOn_const (by rw [hv]; exact ENNReal.one_ne_top))
  exact hg.mono' (measurable_psiIntG Φ RB hd D hSb γ δ layer tt amp frq z κs).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => norm_psiIntG_le Φ RB hd D hSb γ δ layer tt amp frq z κs p)

/-- The interior time integral of the modulated summand of unit `j`. -/
def unitIG (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain) (L γ δ : ℝ)
    (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (layer : GNode (D.forest hS) → ℕ)
    (base : Mom d) {roots : Fin w → (Fin d → ℤ)}
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (z : GenDecoration Gsb d roots 0) (τ' : GBranch Gsb.tree → ℝ) (j : J)
    (κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) : ℂ :=
  ∫ τ : CLInternalTime (regionOf (blk j)),
    gUnitG blk D hS Fs L γ δ layer base j (modLam frq (Φ.route hS hSb) j : ℝ) (Φ.bdry L base z.1 j)
      (Φ.clocks τ' j) κ τ

/-- The fiber integrand over `G_sb` times. -/
def fibIntG (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (L γ δ : ℝ) (base : Mom d) (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (τ' : GBranch Gsb.tree → ℝ) : ℂ :=
  (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
    (openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt).indicator
      (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
        ∏ j, (Φ.recJ L γ δ base z τ' j * unitIG Φ D hS hSb L γ δ Fs layer base frq z τ' j (κs j))) τ'

theorem inner_psiIntG (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (τ' : GBranch Gsb.tree → ℝ) :
    ∫ τs : (∀ j, CLInternalTime (regionOf (blk j))),
      psiIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs (τ', τs) =
    fibIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs τ' := by
  unfold psiIntG fibIntG
  by_cases hp : τ' ∈ openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt
  · simp only [Set.indicator_of_mem hp]
    rw [integral_const_mul, integral_const_mul]
    congr 2
    have := integral_fintype_prod_volume_eq_prod (𝕜 := ℂ) (ι := J)
      (E := fun j => CLInternalTime (regionOf (blk j)))
      (fun j (τ : CLInternalTime (regionOf (blk j))) =>
        unitIntG Φ D hS Fs L γ δ layer base frq hSb z τ' j (κs j) τ)
    rw [this]
    refine Finset.prod_congr rfl fun j _ => ?_
    unfold unitIntG SpliceShape.recJ unitIG
    rw [integral_const_mul]
  · simp only [Set.indicator_of_notMem hp]
    simp

theorem integral_psiIntG (RB : RegBound blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    ∫ p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))),
      psiIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs p =
    ∫ τ' : GBranch Gsb.tree → ℝ, fibIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs τ' := by
  rw [Measure.volume_eq_prod, integral_prod _ (integrable_psiIntG Φ RB hd D hSb γ δ layer tt amp frq z κs)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun τ' =>
    inner_psiIntG Φ hd D hSb γ δ layer tt amp frq z κs τ')

theorem norm_unitIG_le (RB : RegBound blk hS Fs L base) (D : ReconstructionData S) (hSb : Gsb.IsPlain)
    (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (z : GenDecoration Gsb d roots 0) (τ' : GBranch Gsb.tree → ℝ) (j : J)
    (κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    ‖unitIG Φ D hS hSb L γ δ Fs layer base frq z τ' j κ‖ ≤ RB.lb j (clExtendIndices (regionOf (blk j)) κ.1) :=
  norm_integral_gUnitG_le RB D γ δ layer j _ _ _ κ

theorem norm_fibIntG_le (RB : RegBound blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) (τ' : GBranch Gsb.tree → ℝ) :
    ‖fibIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs τ'‖ ≤
      (boxSb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)).indicator
        (fun _ => ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1)) τ' := by
  have hlb0 : 0 ≤ ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) :=
    mul_nonneg (ampBound_nonneg _ _ _ _ _) (Finset.prod_nonneg fun j _ => RB.nonneg j _)
  unfold fibIntG
  by_cases hp : τ' ∈ openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt
  · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (openSb_subset_box _ _ hp)]
    have h1 : ‖(splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_splicedEpsilon_le _ _ _
    have h2 : ‖Φ.sbInt hS hSb L γ δ base tt amp frq z τ'‖ ≤ ampBound hSb L base amp z := by
      unfold SpliceShape.sbInt ampBound
      rw [norm_mul, norm_mul, norm_phaseProd_le, norm_routedPhase, norm_prod]
      simp
    have h3 : ∏ j, ‖Φ.recJ L γ δ base z τ' j * unitIG Φ D hS hSb L γ δ Fs layer base frq z τ' j (κs j)‖ ≤
        ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) := by
      refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => ?_
      rw [norm_mul, Φ.norm_recJ, one_mul]
      exact norm_unitIG_le Φ RB D hSb γ δ layer frq z τ' j (κs j)
    rw [norm_mul, norm_mul, norm_prod]
    calc _ ≤ 1 * (ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1)) :=
          mul_le_mul h1 (mul_le_mul h2 h3 (Finset.prod_nonneg fun _ _ => norm_nonneg _)
            (ampBound_nonneg _ _ _ _ _)) (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
            zero_le_one
      _ = _ := one_mul _
  · rw [Set.indicator_of_notMem hp]
    simp only [mul_zero, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hlb0) _

theorem integrable_fibIntG (RB : RegBound blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    Integrable (fibIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs) := by
  have := (integrable_psiIntG Φ RB hd D hSb γ δ layer tt amp frq z κs).integral_prod_left
  have hfun : (fun τ' => ∫ τs : (∀ j, CLInternalTime (regionOf (blk j))),
      psiIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs (τ', τs)) =
      fibIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs :=
    funext fun τ' => inner_psiIntG Φ hd D hSb γ δ layer tt amp frq z κs τ'
  rwa [hfun] at this

theorem summable_unitIG (RB : RegBound blk hS Fs L base) (D : ReconstructionData S) (hSb : Gsb.IsPlain)
    (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (z : GenDecoration Gsb d roots 0) (τ' : GBranch Gsb.tree → ℝ) (j : J) :
    Summable fun κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j) =>
      unitIG Φ D hS hSb L γ δ Fs layer base frq z τ' j κ :=
  Summable.of_norm_bounded (RB.summable j _) fun κ => norm_unitIG_le Φ RB D hSb γ δ layer frq z τ' j κ

theorem fiber_sumG (RB : RegBound blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0) :
    ∑' κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)),
      ∫ p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))),
        psiIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs p =
    ∫ τ' : GBranch Gsb.tree → ℝ, (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
      (openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt).indicator
        (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
          ∏ j, (Φ.recJ L γ δ base z τ' j *
            ∑' κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j),
              unitIG Φ D hS hSb L γ δ Fs layer base frq z τ' j κ)) τ' := by
  have hK : Summable fun κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
      ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) :=
    ((summable_pi_prod_dep (fun j (κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
      RB.lb j (clExtendIndices (regionOf (blk j)) κ.1))
      (fun j κ => RB.nonneg j _) (fun j => RB.summable j _)).1).mul_left _
  have hsum : Summable fun κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
      ∫ τ' : GBranch Gsb.tree → ℝ, ‖fibIntG Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs τ'‖ := by
    refine Summable.of_nonneg_of_le (fun κs => integral_nonneg fun _ => norm_nonneg _) (fun κs => ?_) hK
    have hgi : Integrable ((boxSb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)).indicator
        (fun _ => ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1))) :=
      (integrable_indicator_iff (measurableSet_boxSb _)).2
        (integrableOn_const (by rw [volume_boxSb]; exact ENNReal.one_ne_top))
    refine (integral_mono (integrable_fibIntG Φ RB hd D hSb γ δ layer tt amp frq z κs).norm hgi
      fun τ' => norm_fibIntG_le Φ RB hd D hSb γ δ layer tt amp frq z κs τ').trans_eq ?_
    rw [integral_indicator_const _ (measurableSet_boxSb _), Measure.real, volume_boxSb]
    simp
  simp_rw [integral_psiIntG Φ RB hd D hSb γ δ layer tt amp frq z]
  rw [integral_tsum_of_summable_integral_norm
    (fun κs => integrable_fibIntG Φ RB hd D hSb γ δ layer tt amp frq z κs) hsum]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ' => ?_)
  by_cases hp : τ' ∈ openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt
  · unfold fibIntG
    simp only [Set.indicator_of_mem hp]
    rw [tsum_mul_left, tsum_mul_left]
    congr 2
    have hs : ∀ j, Summable fun κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j) =>
        Φ.recJ L γ δ base z τ' j * unitIG Φ D hS hSb L γ δ Fs layer base frq z τ' j κ :=
      fun j => (summable_unitIG Φ RB D hSb γ δ layer frq z τ' j).mul_left _
    rw [tsum_pi_prod_complex (fun j κ => Φ.recJ L γ δ base z τ' j *
      unitIG Φ D hS hSb L γ δ Fs layer base frq z τ' j κ) hs]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [tsum_mul_left]
  · unfold fibIntG
    simp [Set.indicator_of_notMem hp]

end Fiber

end WaveTurbulence.Flower.Stage1WVine
