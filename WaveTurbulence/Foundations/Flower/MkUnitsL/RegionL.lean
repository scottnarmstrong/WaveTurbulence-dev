/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnitsL.WIntegW
public import WaveTurbulence.Foundations.Flower.Stage1WVine.WRegion3
public import WaveTurbulence.Foundations.Flower.V5W2L.Defs

/-! # MK-UNITS-L (B3-2): the weighted slot family with per-unit top filters, and its unit kernel

* `slotFWW`: Stage1WVine's frontier-weighted slot family `slotFW` with a top weight `Wt` (a `SlotFamW`).
* `regBoundFWW`: the regional bound `RegBoundW` (Stage1WVine's `regBoundFW`; the top weight has norm `≤ 1`).
* `unitKernelMG_slotFWW_eq`: for the blocks of the unit regions of a state `X`, the generic unit factor of
  `slotFWW … Wt` is V5W-2L's pinned `unitRecenteredFWL p (g j₁) (SU j) X (us j) … (modW λ)` whenever the top weight at
  the unit's top is `topFilterWeightL (SU j)` (Stage1WVine's `unitKernelMG_slotFW_eq` with the product filter).
* `topWeightOf`: the branch-indexed top weight carrying `topFilterWeightL (SU j)` at the top of unit `j`.

Adapted from `Flower/Stage1WVine/WRegion3.lean` (see `COPIED-SHA256SUMS`).
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
  WaveTurbulence.VineB WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.VineC
  WaveTurbulence.LFTwist
open WaveTurbulence.Flower.Stage1WVine (slotFW regBoundFW regionCross clLocalStarProductG_slotFW
  regionWeightFW_eq_regionCross unitCψ)
open WaveTurbulence.Flower.V5W2L (topFilterWeightL regionWeightFWL unitKernelFWL unitRecenteredFWL)
open WaveTurbulence.VineSpaceK (nodeWeight)

/-! ## The top weights -/

section TopWeight
variable {w d : ℕ} {S : Garden w} {J : Type}

open scoped Classical in
/-- The branch-indexed top weight carrying `topFilterWeightL (SU j)` at the top `top j` of unit `j` (no filter
elsewhere). -/
def topWeightOf (top : J → GBranch S.tree) (SU : J → List ℝ) : GBranch S.tree → (Fin 4 → Mom d) → ℂ :=
  fun v => if h : ∃ j, top j = v then topFilterWeightL (SU (Classical.choose h)) else topFilterWeightL []

theorem topWeightOf_apply {top : J → GBranch S.tree} (hinj : Function.Injective top) (SU : J → List ℝ) (j : J) :
    topWeightOf (d := d) top SU (top j) = topFilterWeightL (SU j) := by
  classical
  have h : ∃ j', top j' = top j := ⟨j, rfl⟩
  unfold topWeightOf
  rw [dif_pos h, hinj (Classical.choose_spec h)]

theorem norm_topFilterWeightL_leW (S : List ℝ) (z : Fin 4 → Mom d) : ‖topFilterWeightL S z‖ ≤ 1 := by
  have h : ∀ y : ℝ, ‖((WaveTurbulence.chi0 y : ℝ) : ℂ)‖ ≤ 1 := fun y => by
    have h0 : 0 ≤ WaveTurbulence.chi0 y := Real.smoothTransition.nonneg _
    have h1 : WaveTurbulence.chi0 y ≤ 1 := Real.smoothTransition.le_one _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  induction S with
  | nil => simp [topFilterWeightL]
  | cons s S ih =>
    rw [V5W2L.topFilterWeightL_cons, norm_mul]
    exact (mul_le_mul (h _) ih (norm_nonneg _) zero_le_one).trans (one_mul 1).le

theorem norm_topWeightOf_le (top : J → GBranch S.tree) (SU : J → List ℝ) (v : GBranch S.tree) (q : Fin 4 → Mom d) :
    ‖topWeightOf top SU v q‖ ≤ 1 := by
  classical
  unfold topWeightOf
  split_ifs
  · exact norm_topFilterWeightL_leW _ q
  · exact norm_topFilterWeightL_leW _ q

/-- Disjoint blocks have distinct tops. -/
theorem upper_injective {blk : J → CLBlock S} (hd : Disj blk) : Function.Injective fun j => (blk j).upper := by
  intro j k hjk
  by_contra hne
  have he : (blk j).upper = (blk k).upper := hjk
  exact Finset.disjoint_left.mp (hd j k hne) (blk j).isBlock.2.1 (he ▸ (blk k).isBlock.2.1)

end TopWeight

/-! ## The slot family and its regional bound -/

section Bound
variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) (L γ δ : ℝ) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (p : ℕ)
  (gT : Fin w → Mom d → ℂ)

/-- **The frontier-weighted slot family with top weights.** -/
def slotFWW (Wt : GBranch S.tree → (Fin 4 → Mom d) → ℂ) : SlotFamW S d :=
  ⟨slotFW D hS layer hLayer L γ δ h p gT, Wt⟩

theorem starProdGW_mk (fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (tw : GBranch S.tree → (Fin 4 → Mom d) → ℂ)
    (L' : ℝ) (base : Mom d) (U : Finset (GBranch S.tree)) (a : GBranch S.tree) (top : ℝ)
    (x : GNode S.tree → (Fin d → ℤ)) (u : GBranch S.tree → ℝ) :
    starProdGW hS ⟨fs, tw⟩ L' base U a top x u =
      Stage1WVine.starProdG hS fs L' base U a top x u * nodeWeight (tw a) L' base a x := by
  unfold starProdGW Stage1WVine.starProdG
  rfl

theorem clLocalStarProductGW_mk {U : Finset (GBranch S.tree)} {a b : GBranch S.tree} (R : CLRegionData S U a b)
    (fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (tw : GBranch S.tree → (Fin 4 → Mom d) → ℂ)
    (L' : ℝ) (base : Mom d) (x : GNode S.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (τ : CLInternalTime R) :
    clLocalStarProductGW hS R ⟨fs, tw⟩ L' base x t τ =
      Stage1WVine.clLocalStarProductG hS R fs L' base x t τ * nodeWeight (tw a) L' base a x := by
  unfold clLocalStarProductGW Stage1WVine.clLocalStarProductG
  exact starProdGW_mk hS fs tw L' base U a (t 0) x (clLocalClock R t τ)

variable {J : Type} [Fintype J] [DecidableEq J]

/-- **The regional bound of the frontier-weighted slot family with top weights of norm `≤ 1`** (Stage1WVine's
`regBoundFW`). -/
def regBoundFWW (blk : J → CLBlock S) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖gT j x‖ ≤ cψ) (base : Mom d)
    (hL : L ≠ 0) (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (Wt : GBranch S.tree → (Fin 4 → Mom d) → ℂ) (hWt : ∀ v q, ‖Wt v q‖ ≤ 1) :
    RegBoundW blk hS (slotFWW D hS layer hLayer L γ δ h p gT Wt) L base where
  lb := (regBoundFW D hS layer hLayer L γ δ h p gT blk cψ hc hg base hL hF).lb
  lbC := (regBoundFW D hS layer hLayer L γ δ h p gT blk cψ hc hg base hL hF).lbC
  nonneg := (regBoundFW D hS layer hLayer L γ δ h p gT blk cψ hc hg base hL hF).nonneg
  norm_le j x top u := by
    unfold slotFWW
    rw [starProdGW_mk, norm_mul]
    calc _ ≤ (regBoundFW D hS layer hLayer L γ δ h p gT blk cψ hc hg base hL hF).lb j x * 1 :=
          mul_le_mul ((regBoundFW D hS layer hLayer L γ δ h p gT blk cψ hc hg base hL hF).norm_le j x top u)
            (hWt _ _) (norm_nonneg _) ((regBoundFW D hS layer hLayer L γ δ h p gT blk cψ hc hg base hL hF).nonneg j x)
      _ = _ := mul_one _
  summable := (regBoundFW D hS layer hLayer L γ δ h p gT blk cψ hc hg base hL hF).summable
  tsum_le := (regBoundFW D hS layer hLayer L γ δ h p gT blk cψ hc hg base hL hF).tsum_le
  meas j := (regBoundFW D hS layer hLayer L γ δ h p gT blk cψ hc hg base hL hF).meas j

end Bound

/-! ## The unit factor of the weighted slot family with top filters is the pinned kernel -/

section Unit

/-- Pulling two time-independent factors out of an indicator. -/
theorem indicator_mid_mulW {α : Type*} (s : Set α) (P Q : α → ℂ) (c n e ε : ℂ) (τ : α) :
    e * (ε * s.indicator (fun τ => P τ * (c * Q τ * n)) τ) = c * n * (ε * s.indicator (fun τ => P τ * Q τ) τ * e) := by
  by_cases hτ : τ ∈ s
  · simp only [Set.indicator_of_mem hτ]
    ring
  · simp only [Set.indicator_of_notMem hτ, mul_zero, zero_mul]

/-- The region multiplier with a product of top filters is V5W-0's at `S = none` times the product filter at the top
(V5W-2L's `regionWeightFWL_eq_none_mul`). -/
theorem regionWeightFWL_eq_none_mulW {w d : ℕ} {ι : Type*} (p : ℕ) (g : Mom d → ℂ) (S : List ℝ) (L : ℝ)
    (base : Mom d) (X : FamilyReconstruction w ι) (U : Finset (GBranch X.skeleton.tree)) (a : GBranch X.skeleton.tree)
    (x : GNode X.skeleton.tree → Fin d → ℤ) :
    regionWeightFWL p g S L base X U a x =
      regionWeightFW p g none L base X U a x * nodeWeight (topFilterWeightL S) L base a x := by
  have h1 : nodeWeight (topFilterWeight (none : Option ℝ)) L base a x = 1 := by
    simp [nodeWeight, topFilterWeight]
  unfold regionWeightFWL regionWeightFW
  rw [h1, mul_one]

variable {w d : ℕ} {ι : Type*} {J : Type} [Fintype J] [DecidableEq J] {Q : J → ι → Prop}

/-- **The generic unit factor of the frontier-weighted slot family with per-unit top filters is V5W-2L's pinned
`unitRecenteredFWL`** (Stage1WVine's `unitKernelMG_slotFW_eq` with the product filter `topFilterWeightL (SU j)` read
at the top of unit `j`). -/
theorem unitKernelMG_slotFWW_eq (X : FamilyReconstruction w ι) (us : ∀ j, UnitAt X.skeleton X.family (Q j))
    (layer : GNode (X.data.forest X.plain) → ℕ) (hL : IsLayering (X.data.garden X.plain) layer)
    (hspec : layeredReconstruction X.data X.plain layer hL = X.layered) (L γ δ : ℝ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (p : ℕ) (gT : Fin w → Mom d → ℂ) (base : Mom d)
    (hcan : IsCanonGC (p + 1) X.layered) (hlay : ∀ x, layer x ≤ p)
    (Wt : GBranch X.skeleton.tree → (Fin 4 → Mom d) → ℂ) (SU : J → List ℝ)
    (hWt : ∀ j, Wt (us j).blk.a = topFilterWeightL (SU j))
    (j : J) (lam : ℤ) (t : Fin 3 → ℝ) (k : Fin 4 → Mom d) :
    unitKernelMGW (fun j => unitClBlock (us j)) X.data X.plain (slotFWW X.data X.plain layer hL L γ δ h p gT Wt)
        L γ δ layer base j lam t k =
      unitRecenteredFWL p (gT (us j).blk.a.1.1) (SU j) X (us j) L γ δ
        (unitProfile (fun j => unitClBlock (us j)) h j) base (modW lam) (t 0) (t 1) (t 2)
        (k 0) (k 1) (k 2) (k 3) := by
  have hl : layer = stateLayer X := layeredReconstruction_inj X.data X.plain (hspec.trans (stateLayer_spec X).symm)
  subst hl
  have hcan' : IsCanonGC (p + 1) (layeredReconstruction X.data X.plain (stateLayer X) hL) := by
    rw [hspec]; exact hcan
  have hk : ![k 0, k 1, k 2, k 3] = k := by funext i; fin_cases i <;> rfl
  have ht : ![t 0, t 1, t 2] = t := by funext i; fin_cases i <;> rfl
  unfold unitKernelMGW unitRecenteredFWL unitKernelFWL clLocalKernelFW unitConst
  rw [hk, ht]
  rw [regionData_subsingleton (regionOf (unitClBlock (us j))) (clRegionData X.skeleton (us j).blk.block (us j).cl)]
  congr 2
  refine tsum_congr fun κ => integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  unfold clLocalSummandGW clLocalSummandFW slotFWW
  simp only [clLocalStarProductGW_mk, clLocalStarProductG_slotFW X.data X.plain (stateLayer X) hL L γ δ h p gT
    (unitClBlock (us j)) hcan' hlay]
  dsimp only [unitClBlock, unitProfile]
  have hrw : regionWeightFW p (gT (us j).blk.a.1.1) none L base X (us j).blk.U (us j).blk.a
      (clExtendIndices (clRegionData X.skeleton (us j).blk.block (us j).cl) κ.1) =
      regionCross X.data X.plain (stateLayer X) hL p (gT (us j).blk.a.1.1) (us j).blk.U (us j).blk.a L base
        (clExtendIndices (clRegionData X.skeleton (us j).blk.block (us j).cl) κ.1) :=
    regionWeightFW_eq_regionCross X ⟨(us j).blk.U, (us j).blk.a, (us j).blk.b, (us j).blk.block, (us j).cl⟩ p
      (gT (us j).blk.a.1.1) L base hcan' hlay (clRegionData X.skeleton (us j).blk.block (us j).cl) _ κ
  rw [regionWeightFWL_eq_none_mulW, hrw, hWt j]
  exact indicator_mid_mulW _ _ _ _ _ _ _ τ

end Unit

end WaveTurbulence.Flower.MkUnitsL
