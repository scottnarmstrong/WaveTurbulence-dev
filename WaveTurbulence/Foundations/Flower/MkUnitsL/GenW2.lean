/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnitsL.GenW1

/-! # MK-UNITS-L (B3-2), generic VINE-B♯ with per-unit top weights: VINE-B♯ with an arbitrary regional slot family — bounds and Fubini

Copy-generalization of `Vine/B/{Unit, Fiber1–6}` from the native kernels to an arbitrary slot family `Fs`, under the
abstract regional bound `RegBoundW` (a pointwise bound of the regional star product by a function `lb j` of the local
decoration, summable over the local decorations of every boundary datum, and measurability of `Fs` in the clocks).
For the native kernels `RegBoundW` is V5's `localBound` (`summable_tsum_localBound`); for the frontier-weighted kernels
it is `cψ`-powers times the same (row file `WRow*`).

Stage1WVine's `GenVB2` with the slot family `Fs` a `SlotFamW` (slot kernels and per-unit top weights, `GenW1`); the
proofs are verbatim, every declaration renamed with the suffix `W`.  Adapted from `Flower/Stage1WVine/GenVB2.lean`
(see `COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.MkUnitsL
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

/-- **The abstract regional bound** of a slot family on the units `blk`. -/
structure RegBoundW (blk : J → CLBlock S) (hS : S.IsPlain) (Fs : SlotFamW S d)
    (L : ℝ) (base : Mom d) where
  lb : J → (GNode S.tree → (Fin d → ℤ)) → ℝ
  lbC : J → ℝ
  nonneg : ∀ j x, 0 ≤ lb j x
  norm_le : ∀ j x top u, ‖starProdGW hS Fs L base (blk j).atoms (blk j).upper top x u‖ ≤ lb j x
  summable : ∀ j (β : Fin 4 → Mom d), Summable fun κ : CLLocalDecoration (regionOf (blk j)) L base β =>
    lb j (clExtendIndices (regionOf (blk j)) κ.1)
  tsum_le : ∀ j (β : Fin 4 → Mom d), ∑' κ : CLLocalDecoration (regionOf (blk j)) L base β,
    lb j (clExtendIndices (regionOf (blk j)) κ.1) ≤ lbC j
  meas : ∀ j, RegMeasW hS Fs L base (blk j).atoms (blk j).upper

section UnitBounds
variable {hS : S.IsPlain} {Fs : SlotFamW S d} {L : ℝ} {base : Mom d}

theorem lbC_nonnegW (RB : RegBoundW blk hS Fs L base) (j : J) (β : Fin 4 → Mom d) : 0 ≤ RB.lbC j :=
  (tsum_nonneg fun κ => RB.nonneg j _).trans (RB.tsum_le j β)

theorem norm_clLocalSummandG_leW (RB : RegBoundW blk hS Fs L base) (D : ReconstructionData S)
    (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) (j : J) (β : Fin 4 → Mom d) (t : Fin 3 → ℝ)
    (κ : CLLocalDecoration (regionOf (blk j)) L base β) (τ : CLInternalTime (regionOf (blk j))) :
    ‖clLocalSummandGW D hS (regionOf (blk j)) Fs L γ δ layer base β t κ τ‖ ≤
      (boxU D hS layer blk j).indicator (fun _ => RB.lb j (clExtendIndices (regionOf (blk j)) κ.1)) τ := by
  classical
  unfold clLocalSummandGW
  by_cases hτ : τ ∈ clLocalTimeDomain (regionOf (blk j)) (fun v => layer (D.coreBranch hS v).toNode) t
  · have hbox : τ ∈ boxU D hS layer blk j := localTimeDomain_subset_box (regionOf (blk j)) _ t hτ
    rw [Set.indicator_of_mem hτ, Set.indicator_of_mem hbox, norm_mul, norm_mul, norm_clRegionalPhase, one_mul]
    calc _ ≤ 1 * RB.lb j (clExtendIndices (regionOf (blk j)) κ.1) :=
          mul_le_mul (norm_clRegionalEpsilon_le _ _) (RB.norm_le j _ _ _) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · rw [Set.indicator_of_notMem hτ, mul_zero, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => RB.nonneg j _) _

theorem norm_gUnitG_leW (RB : RegBoundW blk hS Fs L base) (D : ReconstructionData S)
    (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) (j : J) (lam : ℝ) (β : Fin 4 → Mom d) (t : Fin 3 → ℝ)
    (κ : CLLocalDecoration (regionOf (blk j)) L base β) (τ : CLInternalTime (regionOf (blk j))) :
    ‖gUnitGW blk D hS Fs L γ δ layer base j lam β t κ τ‖ ≤
      (boxU D hS layer blk j).indicator (fun _ => RB.lb j (clExtendIndices (regionOf (blk j)) κ.1)) τ := by
  unfold gUnitGW
  rw [norm_mul, norm_lowModC, one_mul]
  exact norm_clLocalSummandG_leW RB D γ δ layer j β t κ τ

theorem measurable_gUnitGW (RB : RegBoundW blk hS Fs L base) (D : ReconstructionData S)
    (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) (j : J) (lam : ℝ) (β : Fin 4 → Mom d) (t : Fin 3 → ℝ)
    (κ : CLLocalDecoration (regionOf (blk j)) L base β) :
    Measurable fun τ : CLInternalTime (regionOf (blk j)) => gUnitGW blk D hS Fs L γ δ layer base j lam β t κ τ := by
  have ht : ∀ i, Measurable fun _ : CLInternalTime (regionOf (blk j)) => t i := fun i => measurable_const
  have hτ : ∀ v, Measurable fun τ : CLInternalTime (regionOf (blk j)) => τ v := fun v => measurable_pi_apply v
  have h1 := measurable_clLocalSummandG_jointW D hS (regionOf (blk j)) Fs L γ δ base (RB.meas j) layer β κ
    (fun _ : CLInternalTime (regionOf (blk j)) => t) (fun τ => τ) ht hτ
  have hm : Measurable fun τ : CLInternalTime (regionOf (blk j)) => lowModC (regionOf (blk j)) lam t τ := by
    have hb := measurable_clLocalClock_joint (regionOf (blk j)) (fun _ : CLInternalTime (regionOf (blk j)) => t)
      (fun τ => τ) ht hτ (blk j).lower
    unfold lowModC
    exact Measurable.cexp ((Complex.measurable_ofReal.comp (hb.const_mul (Real.pi * lam))).mul_const Complex.I)
  exact hm.mul h1

theorem integrable_gUnitGW (RB : RegBoundW blk hS Fs L base) (D : ReconstructionData S)
    (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) (j : J) (lam : ℝ) (β : Fin 4 → Mom d) (t : Fin 3 → ℝ)
    (κ : CLLocalDecoration (regionOf (blk j)) L base β) :
    Integrable fun τ : CLInternalTime (regionOf (blk j)) => gUnitGW blk D hS Fs L γ δ layer base j lam β t κ τ := by
  have hB : MeasurableSet (boxU D hS layer blk j) := by
    unfold boxU
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hg : Integrable ((boxU D hS layer blk j).indicator
      (fun _ => RB.lb j (clExtendIndices (regionOf (blk j)) κ.1))) :=
    (integrable_indicator_iff hB).2 (integrableOn_const (by rw [volume_boxU]; exact ENNReal.one_ne_top))
  exact hg.mono' (measurable_gUnitGW RB D γ δ layer j lam β t κ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun τ => norm_gUnitG_leW RB D γ δ layer j lam β t κ τ)

theorem norm_integral_gUnitG_leW (RB : RegBoundW blk hS Fs L base) (D : ReconstructionData S)
    (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) (j : J) (lam : ℝ) (β : Fin 4 → Mom d) (t : Fin 3 → ℝ)
    (κ : CLLocalDecoration (regionOf (blk j)) L base β) :
    ‖∫ τ : CLInternalTime (regionOf (blk j)), gUnitGW blk D hS Fs L γ δ layer base j lam β t κ τ‖ ≤
      RB.lb j (clExtendIndices (regionOf (blk j)) κ.1) := by
  have hB : MeasurableSet (boxU D hS layer blk j) := by
    unfold boxU
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hg : Integrable ((boxU D hS layer blk j).indicator
      (fun _ => RB.lb j (clExtendIndices (regionOf (blk j)) κ.1))) :=
    (integrable_indicator_iff hB).2 (integrableOn_const (by rw [volume_boxU]; exact ENNReal.one_ne_top))
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_mono (integrable_gUnitGW RB D γ δ layer j lam β t κ).norm hg
    fun τ => norm_gUnitG_leW RB D γ δ layer j lam β t κ τ).trans_eq ?_
  rw [integral_indicator_const _ hB, Measure.real, volume_boxU]
  simp

end UnitBounds

section Fiber
variable (Φ : SpliceShape blk Gsb)

variable {hS : S.IsPlain} {Fs : SlotFamW S d} {L : ℝ} {base : Mom d}

/-- The interior time integral of the modulated summand of unit `j`. -/
def unitIGW (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain) (L γ δ : ℝ)
    (Fs : SlotFamW S d) (layer : GNode (D.forest hS) → ℕ)
    (base : Mom d) {roots : Fin w → (Fin d → ℤ)}
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (z : GenDecoration Gsb d roots 0) (τ' : GBranch Gsb.tree → ℝ) (j : J)
    (κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) : ℂ :=
  ∫ τ : CLInternalTime (regionOf (blk j)),
    gUnitGW blk D hS Fs L γ δ layer base j (modLam frq (Φ.route hS hSb) j : ℝ) (Φ.bdry L base z.1 j)
      (Φ.clocks τ' j) κ τ

theorem norm_unitIG_leW (RB : RegBoundW blk hS Fs L base) (D : ReconstructionData S) (hSb : Gsb.IsPlain)
    (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (z : GenDecoration Gsb d roots 0) (τ' : GBranch Gsb.tree → ℝ) (j : J)
    (κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    ‖unitIGW Φ D hS hSb L γ δ Fs layer base frq z τ' j κ‖ ≤ RB.lb j (clExtendIndices (regionOf (blk j)) κ.1) :=
  norm_integral_gUnitG_leW RB D γ δ layer j _ _ _ κ

theorem summable_unitIGW (RB : RegBoundW blk hS Fs L base) (D : ReconstructionData S) (hSb : Gsb.IsPlain)
    (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (z : GenDecoration Gsb d roots 0) (τ' : GBranch Gsb.tree → ℝ) (j : J) :
    Summable fun κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j) =>
      unitIGW Φ D hS hSb L γ δ Fs layer base frq z τ' j κ :=
  Summable.of_norm_bounded (RB.summable j _) fun κ => norm_unitIG_leW Φ RB D hSb γ δ layer frq z τ' j κ

end Fiber

end WaveTurbulence.Flower.MkUnitsL
