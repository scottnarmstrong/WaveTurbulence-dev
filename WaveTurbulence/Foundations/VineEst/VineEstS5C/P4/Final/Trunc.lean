/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.Export
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.WinChain
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.Member
public import WaveTurbulence.Foundations.Spine.PL234Draft.SameLayerApprox

/-! # V5 FINAL (e): F-trunc, the kernel depends on the input family only at layers `≤ p`

`VineEstCanonLayerC2M` bounds `h r` only for `r ≤ p`, while the flattening `twistedRecenteredModC_eq_flat` asks for coset summability of
`F k` for all `k`.  Every member of the class has all its native objects in layers `≤ p`, so the modulated class integrand is unchanged
when `F` is replaced by the truncation `F' k = if k ≤ p then F k else 0`:
`clLocalStarProduct_congr_F`, `clLocalSummand_congr_F`, `clLocalKernelModC_congr_F`, `twistedRecenteredModC_congr_F`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.P4.Final
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract WaveTurbulence.LGSpine
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4 WaveTurbulence.PL234 WaveTurbulence.VineEstS5C.FlatMod

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {d : ℕ}

/-- The truncation of an input family above layer `p`. -/
def truncF (p : ℕ) (F : ℕ → Mom d → ℝ) : ℕ → Mom d → ℝ := fun k => if k ≤ p then F k else 0

theorem truncF_eq {p : ℕ} (F : ℕ → Mom d → ℝ) : ∀ r ≤ p, truncF p F r = F r := fun r hr => by simp [truncF, hr]

/-- The selected couple row depends on the input family only through its values at the layers of the couple (ruling F2:
the plain and the top-weighted kernels both read `F` at those layers). -/
theorem KQsel_congr_F (incoh q q' : ℕ) (L γ δ : ℝ) (F F' : ℕ → Mom d → ℝ) (LG : LayeredGarden 2)
    (h : ∀ n : GNode LG.garden.tree, F (LG.layer n) = F' (LG.layer n)) (t s : ℝ) (k : Mom d) :
    VineEst.KQsel incoh q q' L γ δ F LG t s k = VineEst.KQsel incoh q q' L γ δ F' LG t s k := by
  have hK : KQstar L γ δ F LG t s k = KQstar L γ δ F' LG t s k :=
    kernelK_congr_inputs L γ δ F F' _ _ _ _ _ _ fun ℓ _ => h _
  have hP : LGSpine.layerProfiles LG F = LGSpine.layerProfiles LG F' := by
    funext z
    unfold LGSpine.layerProfiles
    split_ifs
    · exact h _
    · rfl
  unfold VineEst.KQsel
  rw [hK, hP]

/-- The selected tree row depends on the input family only through its values at the layers of the tree. -/
theorem KTsel_congr_F (incoh q : ℕ) (L γ δ : ℝ) (F F' : ℕ → Mom d → ℝ) (LG : LayeredGarden 1)
    (h : ∀ n : GNode LG.garden.tree, F (LG.layer n) = F' (LG.layer n)) (t s : ℝ) (k : Mom d) :
    VineEst.KTsel incoh q L γ δ F LG t s k = VineEst.KTsel incoh q L γ δ F' LG t s k := by
  have hK : KTstar L γ δ F LG t s k = KTstar L γ δ F' LG t s k :=
    kernelK_congr_inputs L γ δ F F' _ _ _ _ _ _ fun ℓ _ => h _
  have hP : LGSpine.layerProfiles LG F = LGSpine.layerProfiles LG F' := by
    funext z
    unfold LGSpine.layerProfiles
    split_ifs
    · exact h _
    · rfl
  unfold VineEst.KTsel
  rw [hK, hP]

theorem clLocalStarProduct_congr_F (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b) (L γ δ : ℝ)
    (F F' : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (κ : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (τ : CLInternalTime R) {p : ℕ} (hlay : ∀ x, layer x ≤ p)
    (hFF : ∀ r ≤ p, F r = F' r) :
    clLocalStarProduct D hG R L γ δ F layer hLayer base κ t τ = clLocalStarProduct D hG R L γ δ F' layer hLayer base κ t τ := by
  unfold clLocalStarProduct
  simp only
  congr 1
  · refine Finset.prod_congr rfl fun q _ => ?_
    unfold VineEst.selCoupleRow
    refine KQsel_congr_F _ _ _ L γ δ F F' _ ?_ _ _ _
    intro n
    exact hFF _ (hlay _)
  · refine Finset.prod_congr rfl fun v _ => ?_
    unfold VineEst.selTreeRow
    refine KTsel_congr_F _ _ L γ δ F F' _ ?_ _ _ _
    intro n
    exact hFF _ (hlay _)

theorem clLocalSummand_congr_F (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b) (L γ δ : ℝ)
    (F F' : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (boundary : Fin 4 → Mom d) (t : Fin 3 → ℝ) (κ : CLLocalDecoration R L base boundary) (τ : CLInternalTime R) {p : ℕ}
    (hlay : ∀ x, layer x ≤ p) (hFF : ∀ r ≤ p, F r = F' r) :
    clLocalSummand D hG R L γ δ F layer hLayer base boundary t κ τ = clLocalSummand D hG R L γ δ F' layer hLayer base boundary t κ τ := by
  have h : ∀ τ' : CLInternalTime R, clLocalStarProduct D hG R L γ δ F layer hLayer base (clExtendIndices R κ.1) t τ' =
      clLocalStarProduct D hG R L γ δ F' layer hLayer base (clExtendIndices R κ.1) t τ' :=
    fun τ' => clLocalStarProduct_congr_F D hG R L γ δ F F' layer hLayer base _ t τ' hlay hFF
  unfold clLocalSummand
  simp only [h]

theorem clLocalKernelModC_congr_F (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b) (L γ δ : ℝ)
    (F F' : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (lam : ℝ) (t0 t1 t2 : ℝ) (e f g h : Mom d) {p : ℕ} (hlay : ∀ x, layer x ≤ p) (hFF : ∀ r ≤ p, F r = F' r) :
    Cont.clLocalKernelModC D hG R L γ δ F layer hLayer base lam t0 t1 t2 e f g h =
      Cont.clLocalKernelModC D hG R L γ δ F' layer hLayer base lam t0 t1 t2 e f g h := by
  unfold Cont.clLocalKernelModC
  refine congrArg (HMul.hMul _) (tsum_congr fun κ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only
  rw [clLocalSummand_congr_F D hG R L γ δ F F' layer hLayer base _ _ κ τ hlay hFF]

/-- **F-trunc for the modulated class integrand**: it depends on `F` only at layers `≤ p`. -/
theorem twistedRecenteredModC_congr_F {ι : Type*} [Fintype ι] {p : ℕ} (A : FamilyReconstruction w ι) (hA : IsPrimeGarden A.skeleton)
    (c : ChainAt A.skeleton A.family) (hAl : ∀ x, stateLayer A x ≤ p) (a : GBranch A.skeleton.tree)
    (L γ δ : ℝ) (F F' : ℕ → Mom d → ℝ) (base : Mom d) (lam : ℝ) (t0 t1 t2 : ℝ) (e f g h : Mom d)
    (hFF : ∀ r ≤ p, F r = F' r) :
    Cont.twistedRecenteredModC A.skeleton a (canonFinsetK p kind A c) L γ δ F base lam t0 t1 t2 e f g h =
      Cont.twistedRecenteredModC A.skeleton a (canonFinsetK p kind A c) L γ δ F' base lam t0 t1 t2 e f g h := by
  unfold Cont.twistedRecenteredModC
  refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun x hx => ?_)
  obtain ⟨M, _, hr⟩ := (mem_canonFinset hA).1 hx
  exact clLocalKernelModC_congr_F _ _ _ L γ δ F F' _ _ base lam t0 t1 t2 e f g h
    (Cont.reach_stateLayer_le hr hAl) hFF

end WaveTurbulence.VineEstS5C.P4.Final
