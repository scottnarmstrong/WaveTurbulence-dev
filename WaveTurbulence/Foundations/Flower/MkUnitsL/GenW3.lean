/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnitsL.GenW2

/-! # MK-UNITS-L (B3-2), generic VINE-B♯ with per-unit top weights: VINE-B♯ per-mode identity with an arbitrary regional slot family

Copy-generalization of `Vine/B/{Main1–5}`:
`skelVal (modalFnGW Fs) = outerValM (…, unitKernelMGW Fs)` (`skelVal_modal_eq_outerValMGW`), where `unitKernelMGW Fs` is
V5's modulated recentered unit kernel with the regional star product built from `Fs`.  The routing of the outer slot
modes to the lower joint of each unit (R58) is main's `modes_glue`, unchanged.

Stage1WVine's `GenVB3` with the slot family `Fs` a `SlotFamW` (slot kernels and per-unit top weights, `GenW1`); the
proofs are verbatim, every declaration renamed with the suffix `W`.  Adapted from `Flower/Stage1WVine/GenVB3.lean`
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

/-- **The unit factor** of the per-mode identity with the slot family `Fs` (cf. `VineB.unitKernelM_eq`). -/
def unitKernelMGW (blk : J → CLBlock S) (D : ReconstructionData S) (hS : S.IsPlain)
    (Fs : SlotFamW S d) (L γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    (base : Mom d) : J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ :=
  fun j lam t β => recExp L γ δ (S.sign (blk j).upper.toNode) (t 0) β *
    (unitConst (d := d) blk L γ δ j *
      ∑' κ : CLLocalDecoration (regionOf (blk j)) L base β, ∫ τ : CLInternalTime (regionOf (blk j)),
        lowModC (regionOf (blk j)) (lam : ℝ) t τ *
          clLocalSummandGW D hS (regionOf (blk j)) Fs L γ δ layer base β t κ τ)

theorem clLocalSummandG_congrW {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (Fs : SlotFamW G d) (L γ δ : ℝ) (layer : GNode (D.forest hG) → ℕ)
    (base : Mom d) (boundary : Fin 4 → Mom d) (t t' : Fin 3 → ℝ) (h0 : t 0 = t' 0)
    (hp : (b.child R.positive).1.2 ∉ (G.tree (b.child R.positive).1.1).branching ∨ t 1 = t' 1)
    (hn : (b.child R.negative).1.2 ∉ (G.tree (b.child R.negative).1.1).branching ∨ t 2 = t' 2)
    (κ : CLLocalDecoration R L base boundary) (τ : CLInternalTime R) :
    clLocalSummandGW D hG R Fs L γ δ layer base boundary t κ τ =
      clLocalSummandGW D hG R Fs L γ δ layer base boundary t' κ τ := by
  have hc := VineEstS3.clLocalClock_congr R t t' h0 hp hn
  have hd := VineEstS3.clLocalTimeDomain_congr R (fun v => layer (D.coreBranch hG v).toNode) t t' h0 hp hn
  unfold clLocalSummandGW clLocalStarProductGW
  simp only [hc, hd, h0]

namespace UnitGW
variable (Φ : SpliceShape blk Gsb)

theorem unitKernelMG_clocksW (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain)
    (Fs : SlotFamW S d) (L γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ)
    (base : Mom d) (tt : Fin w → ℝ) (τ' : GBranch Gsb.tree → ℝ) (j : J) (lam : ℤ) (β : Fin 4 → Mom d) :
    unitKernelMGW blk D hS Fs L γ δ layer base j lam (fun c => clockOf Gsb tt τ' (Φ.hclk hd j c)) β =
      unitKernelMGW blk D hS Fs L γ δ layer base j lam (Φ.clocks τ' j) β := by
  have h0 : clockOf Gsb tt τ' (Φ.hclk hd j 0) = Φ.clocks τ' j 0 := (Φ.clocks_zero hd τ' j).symm
  have hp : ((blk j).lower.child (regionOf (blk j)).positive).1.2 ∉
      (S.tree ((blk j).lower.child (regionOf (blk j)).positive).1.1).branching ∨
      clockOf Gsb tt τ' (Φ.hclk hd j 1) = Φ.clocks τ' j 1 := by
    by_cases hb : ((blk j).lower.child (regionOf (blk j)).positive).1.2 ∈
        (S.tree ((blk j).lower.child (regionOf (blk j)).positive).1.1).branching
    · exact Or.inr (Φ.clock_pos_eq hd tt τ' j hb)
    · exact Or.inl hb
  have hn : ((blk j).lower.child (regionOf (blk j)).negative).1.2 ∉
      (S.tree ((blk j).lower.child (regionOf (blk j)).negative).1.1).branching ∨
      clockOf Gsb tt τ' (Φ.hclk hd j 2) = Φ.clocks τ' j 2 := by
    by_cases hb : ((blk j).lower.child (regionOf (blk j)).negative).1.2 ∈
        (S.tree ((blk j).lower.child (regionOf (blk j)).negative).1.1).branching
    · exact Or.inr (Φ.clock_neg_eq hd tt τ' j hb)
    · exact Or.inl hb
  unfold unitKernelMGW
  simp only [h0]
  congr 2
  refine tsum_congr fun κ => integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  have e1 := lowModC_congr (regionOf (blk j)) (lam : ℝ) (fun c => clockOf Gsb tt τ' (Φ.hclk hd j c))
    (Φ.clocks τ' j) h0 hp hn τ
  have e2 := clLocalSummandG_congrW D hS (regionOf (blk j)) Fs L γ δ layer base β
    (fun c => clockOf Gsb tt τ' (Φ.hclk hd j c)) (Φ.clocks τ' j) h0 hp hn κ τ
  simp only [e1, e2]

theorem prod_unitKernelMGW (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (L γ δ : ℝ) (base : Mom d) (Fs : SlotFamW S d)
    (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (z : GenDecoration Gsb d roots 0) (τ' : GBranch Gsb.tree → ℝ) :
    ∏ j, unitKernelMGW blk D hS Fs L γ δ layer base j (modLam frq (Φ.route hS hSb) j)
        (fun c => clockOf Gsb tt τ' (Φ.hclk hd j c)) (fun c => base + latticePoint L (z.1 (Φ.hmom hd j c))) =
      (∏ j, unitConst (d := d) blk L γ δ j) * ∏ j, (Φ.recJ L γ δ base z τ' j *
        ∑' κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j),
          unitIGW Φ D hS hSb L γ δ Fs layer base frq z τ' j κ) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [unitKernelMG_clocksW Φ hd D hS Fs L γ δ layer base tt τ' j, ← Φ.bdry_eq hd L base z.1 j]
  unfold unitKernelMGW SpliceShape.recJ unitIGW gUnitGW
  ring

variable {hS : S.IsPlain} {Fs : SlotFamW S d} {L : ℝ} {base : Mom d}

theorem resDec_glueDecGW (hd : Disj blk) {L' : ℝ} (hL : L' ≠ 0) (base' : Mom d)
    {roots : Fin w → (Fin d → ℤ)} (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L' base' (Φ.bdry L' base' z.1 j)) :
    Φ.resDec hS hd (Φ.glueDec hS hd hL base' z κs) = z := by
  apply Subtype.ext
  funext y
  show (Φ.glueDec hS hd hL base' z κs).1 (Φ.node y) = z.1 y
  rw [Φ.glueDec_val, Φ.glue_ret _ _ (Φ.ret_node y), Φ.ext_node]

/-- The domination of the glued terms. -/
def kBoundGW (RB : RegBoundW blk hS Fs L base) (hSb : Gsb.IsPlain) {roots : Fin w → (Fin d → ℤ)}
    (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (p : Σ z : GenDecoration Gsb d roots 0, ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    ℝ :=
  ampBound hSb L base amp p.1 * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (p.2 j).1)

theorem kBoundG_nonnegW (RB : RegBoundW blk hS Fs L base) (hSb : Gsb.IsPlain) {roots : Fin w → (Fin d → ℤ)}
    (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (p : Σ z : GenDecoration Gsb d roots 0, ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    0 ≤ kBoundGW Φ RB hSb amp p :=
  mul_nonneg (ampBound_nonneg _ _ _ _ _) (Finset.prod_nonneg fun j _ => RB.nonneg j _)

theorem summable_fib_kBoundGW (RB : RegBoundW blk hS Fs L base) (hSb : Gsb.IsPlain) {roots : Fin w → (Fin d → ℤ)}
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (z : GenDecoration Gsb d roots 0) :
    Summable fun κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
      kBoundGW Φ RB hSb amp ⟨z, κs⟩ := by
  have hs := (summable_pi_prod_dep (fun j (κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
      RB.lb j (clExtendIndices (regionOf (blk j)) κ.1))
      (fun j κ => RB.nonneg j _) (fun j => RB.summable j _)).1
  exact hs.mul_left (ampBound hSb L base amp z)

theorem tsum_fib_kBoundG_leW (RB : RegBoundW blk hS Fs L base) (hSb : Gsb.IsPlain) {roots : Fin w → (Fin d → ℤ)}
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (z : GenDecoration Gsb d roots 0) :
    ∑' κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)),
      kBoundGW Φ RB hSb amp ⟨z, κs⟩ ≤ ampBound hSb L base amp z * ∏ j, RB.lbC j := by
  have e : ∑' κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)),
      kBoundGW Φ RB hSb amp ⟨z, κs⟩ =
      ampBound hSb L base amp z * ∑' κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)),
        ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) := by
    rw [← tsum_mul_left]
    rfl
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ (ampBound_nonneg _ _ _ _ _)
  have hs := summable_pi_prod_dep (fun j (κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
    RB.lb j (clExtendIndices (regionOf (blk j)) κ.1))
    (fun j κ => RB.nonneg j _) (fun j => RB.summable j _)
  refine hs.2.trans ?_
  exact Finset.prod_le_prod₀ (fun j _ => tsum_nonneg fun κ => RB.nonneg j _) fun j _ => RB.tsum_le j _

theorem summable_kBoundGW (RB : RegBoundW blk hS Fs L base) (hSb : Gsb.IsPlain) {roots : Fin w → (Fin d → ℤ)}
    (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (hsum : Summable fun z : GenDecoration Gsb d roots 0 => ampBound hSb L base amp z) :
    Summable (kBoundGW Φ RB hSb (roots := roots) amp) := by
  rw [summable_sigma_of_nonneg (kBoundG_nonnegW Φ RB hSb amp)]
  refine ⟨summable_fib_kBoundGW Φ RB hSb amp, ?_⟩
  exact Summable.of_nonneg_of_le (fun z => tsum_nonneg fun κs => kBoundG_nonnegW Φ RB hSb amp _)
    (fun z => tsum_fib_kBoundG_leW Φ RB hSb amp z) (hsum.mul_right (∏ j, RB.lbC j))

theorem const_splitGW (Φ' : SpliceShape blk Gsb) (hd : Disj blk) (L γ δ : ℝ) :
    (coupling d L γ δ : ℂ) ^ S.order * S.zeta = ((coupling d L γ δ : ℂ) ^ Gsb.order * Gsb.zeta) *
      ∏ j, unitConst (d := d) blk L γ δ j := by
  rw [Φ'.order_split hd, Φ'.zeta_split hd, pow_add]
  unfold unitConst
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

end UnitGW

end WaveTurbulence.Flower.MkUnitsL
