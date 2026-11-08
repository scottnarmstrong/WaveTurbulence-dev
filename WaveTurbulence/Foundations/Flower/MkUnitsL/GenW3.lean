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

theorem outer_term_eqGW (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (L γ δ : ℝ) (base : Mom d) (Fs : SlotFamW S d)
    (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (Zw : GenDecoration Gsb d roots 0 → ℝ) (z : GenDecoration Gsb d roots 0) :
    (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) * (Zw z : ℂ) *
      ∫ τ' : GBranch Gsb.tree → ℝ,
        (splicedTimeDomain Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt).indicator (fun τ' =>
          phaseProd L γ δ Gsb (cosetDecoration Gsb L base z.1) τ' *
            (∏ s, amp s (base + latticePoint L (z.1 (slotNode hSb s)))) *
              routedPhase frq (Φ.route hS hSb) tt τ' *
            ∏ j, unitKernelMGW blk D hS Fs L γ δ layer base j (modLam frq (Φ.route hS hSb) j)
              (fun c => clockOf Gsb tt τ' (Φ.hclk hd j c))
              (fun c => base + latticePoint L (z.1 (Φ.hmom hd j c)))) τ' =
    (∏ j, unitConst (d := d) blk L γ δ j) * ((Zw z : ℂ) * ∫ τ' : GBranch Gsb.tree → ℝ,
      (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
        (openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt).indicator
          (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
            ∏ j, (Φ.recJ L γ δ base z τ' j *
              ∑' κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j),
                unitIGW Φ D hS hSb L γ δ Fs layer base frq z τ' j κ)) τ') := by
  rw [integral_congr_ae (indicator_openSb_ae Gsb _ tt _)]
  simp_rw [prod_unitKernelMGW Φ hd D hS hSb L γ δ base Fs layer tt frq z]
  rw [← integral_const_mul, ← integral_const_mul]
  have : ∀ τ' : GBranch Gsb.tree → ℝ, (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) * (Zw z : ℂ) *
      (openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt).indicator
        (fun τ' => phaseProd L γ δ Gsb (cosetDecoration Gsb L base z.1) τ' *
          (∏ s, amp s (base + latticePoint L (z.1 (slotNode hSb s)))) *
            routedPhase frq (Φ.route hS hSb) tt τ' *
          ((∏ j, unitConst (d := d) blk L γ δ j) * ∏ j, (Φ.recJ L γ δ base z τ' j *
            ∑' κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j),
              unitIGW Φ D hS hSb L γ δ Fs layer base frq z τ' j κ))) τ' =
      (∏ j, unitConst (d := d) blk L γ δ j) * ((Zw z : ℂ) *
        ((splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
        (openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt).indicator
          (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
            ∏ j, (Φ.recJ L γ δ base z τ' j *
              ∑' κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j),
                unitIGW Φ D hS hSb L γ δ Fs layer base frq z τ' j κ)) τ')) := by
    intro τ'
    by_cases hp : τ' ∈ openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt
    · simp only [Set.indicator_of_mem hp]
      unfold SpliceShape.sbInt
      ring
    · simp [Set.indicator_of_notMem hp]
  simp_rw [this]
  rw [integral_const_mul, integral_const_mul]

variable {hS : S.IsPlain} {Fs : SlotFamW S d} {L : ℝ} {base : Mom d}

theorem norm_integral_psiIntG_leW (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (D : ReconstructionData S)
    (hSb : Gsb.IsPlain) (γ δ : ℝ) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    ‖∫ p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))),
      psiIntGW Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs p‖ ≤
      ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) := by
  rw [Measure.volume_eq_prod]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hQ := SpliceShape.measurableSet_boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
  have hv := SpliceShape.volume_boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
  have hgi : Integrable ((SpliceShape.boxQ (blk := blk) D hS layer
      (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)).indicator
      (fun _ => ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1)))
      ((volume : Measure (GBranch Gsb.tree → ℝ)).prod
        (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) :=
    (integrable_indicator_iff hQ).2 (integrableOn_const (by rw [hv]; exact ENNReal.one_ne_top))
  refine (integral_mono (integrable_psiIntGW Φ RB hd D hSb γ δ layer tt amp frq z κs).norm hgi
    fun p => norm_psiIntG_leW Φ RB hd D hSb γ δ layer tt amp frq z κs p).trans_eq ?_
  rw [integral_indicator_const _ hQ, Measure.real, hv]
  simp

theorem resDec_glueDecGW (hd : Disj blk) {L' : ℝ} (hL : L' ≠ 0) (base' : Mom d)
    {roots : Fin w → (Fin d → ℤ)} (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L' base' (Φ.bdry L' base' z.1 j)) :
    Φ.resDec hS hd (Φ.glueDec hS hd hL base' z κs) = z := by
  apply Subtype.ext
  funext y
  show (Φ.glueDec hS hd hL base' z κs).1 (Φ.node y) = z.1 y
  rw [Φ.glueDec_val, Φ.glue_ret _ _ (Φ.ret_node y), Φ.ext_node]

open scoped Classical in
/-- **The glued term** (cf. `VineB.SpliceShape.term_glue`). -/
theorem skelTerm_glueGW (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain) (hL : L ≠ 0)
    (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (selSk : GenDecoration S d roots 0 → Prop) (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    skelTermW blk D hS L γ δ base roots tt layer selSk (modalFnGW Φ hS hSb Fs amp frq) (Φ.glueDec hS hd hL base z κs) =
    (Zw z : ℂ) * ∫ p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))),
      psiIntGW Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs p := by
  have hZz := hZ (Φ.glueDec hS hd hL base z κs)
  rw [resDec_glueDecGW Φ hd hL base z κs] at hZz
  unfold skelTermW
  by_cases hs : selSk (Φ.glueDec hS hd hL base z κs)
  · rw [if_pos hs] at hZz ⊢
    rw [← hZz]
    simp only [Complex.ofReal_one, one_mul]
    rw [← integral_const_mul]
    have hmp := (Φ.measurePreserving_timeSplit hd).symm (Φ.timeSplit hd)
    rw [← hmp.integral_comp']
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    beta_reduce
    rw [Φ.timeSplit_symm hd]
    exact integrand_glueGW Φ hd hS hSb hL γ δ base D layer Fs tt amp frq z κs p.1 p.2
  · rw [if_neg hs] at hZz ⊢
    rw [← hZz]
    simp

open scoped Classical in
theorem norm_skelTerm_glueG_leW (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL : L ≠ 0) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (selSk : GenDecoration S d roots 0 → Prop) (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    ‖skelTermW blk D hS L γ δ base roots tt layer selSk (modalFnGW Φ hS hSb Fs amp frq) (Φ.glueDec hS hd hL base z κs)‖ ≤
      ampBound hSb L base amp z * ∏ j, RB.lb j (clExtendIndices (regionOf (blk j)) (κs j).1) := by
  rw [skelTerm_glueGW Φ RB hd hSb hL γ δ D layer tt amp frq selSk Zw hZ z κs, norm_mul]
  have hZz := hZ (Φ.glueDec hS hd hL base z κs)
  rw [resDec_glueDecGW Φ hd hL base z κs] at hZz
  have h1 : ‖(Zw z : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, ← hZz]
    split_ifs <;> simp
  calc _ ≤ 1 * _ := mul_le_mul h1 (norm_integral_psiIntG_leW Φ RB hd D hSb γ δ layer tt amp frq z κs)
        (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

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

open scoped Classical in
theorem tsum_skelTermGW (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain) (hL : L ≠ 0)
    (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ) {roots : Fin w → (Fin d → ℤ)}
    (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (selSk : GenDecoration S d roots 0 → Prop) (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (hsum : Summable fun z : GenDecoration Gsb d roots 0 => ampBound hSb L base amp z) :
    ∑' κ : GenDecoration S d roots 0, skelTermW blk D hS L γ δ base roots tt layer selSk (modalFnGW Φ hS hSb Fs amp frq) κ =
    ∑' z : GenDecoration Gsb d roots 0, (Zw z : ℂ) *
      ∫ τ' : GBranch Gsb.tree → ℝ, (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
        (openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt).indicator
          (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
            ∏ j, (Φ.recJ L γ δ base z τ' j *
              ∑' κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j),
                unitIGW Φ D hS hSb L γ δ Fs layer base frq z τ' j κ)) τ' := by
  have hglue : ∀ p : (Σ z : GenDecoration Gsb d roots 0,
      ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)),
      skelTermW blk D hS L γ δ base roots tt layer selSk (modalFnGW Φ hS hSb Fs amp frq)
        ((Φ.decSplit hS hd hL base roots).symm p) = (Zw p.1 : ℂ) *
      ∫ q : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))),
        psiIntGW Φ hd D hS hSb L γ δ base Fs layer tt amp frq p.1 p.2 q :=
    fun p => skelTerm_glueGW Φ RB hd hSb hL γ δ D layer tt amp frq selSk Zw hZ p.1 p.2
  have hnorm : ∀ p : (Σ z : GenDecoration Gsb d roots 0,
      ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)),
      ‖skelTermW blk D hS L γ δ base roots tt layer selSk (modalFnGW Φ hS hSb Fs amp frq)
        ((Φ.decSplit hS hd hL base roots).symm p)‖ ≤ kBoundGW Φ RB hSb amp p :=
    fun p => norm_skelTerm_glueG_leW Φ RB hd hSb hL γ δ D layer tt amp frq selSk Zw hZ p.1 p.2
  have hFs : Summable fun p => skelTermW blk D hS L γ δ base roots tt layer selSk (modalFnGW Φ hS hSb Fs amp frq)
      ((Φ.decSplit hS hd hL base roots).symm p) :=
    Summable.of_norm_bounded (summable_kBoundGW Φ RB hSb (roots := roots) amp hsum) hnorm
  have hfib : ∀ z : GenDecoration Gsb d roots 0,
      Summable fun κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
        skelTermW blk D hS L γ δ base roots tt layer selSk (modalFnGW Φ hS hSb Fs amp frq)
          ((Φ.decSplit hS hd hL base roots).symm ⟨z, κs⟩) :=
    fun z => Summable.of_norm_bounded (summable_fib_kBoundGW Φ RB hSb amp z) fun κs => hnorm ⟨z, κs⟩
  have e2 := Summable.tsum_sigma' (f := fun p : (Σ z : GenDecoration Gsb d roots 0,
      ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
      skelTermW blk D hS L γ δ base roots tt layer selSk (modalFnGW Φ hS hSb Fs amp frq)
        ((Φ.decSplit hS hd hL base roots).symm p)) hfib hFs
  have e1 := (Φ.decSplit hS hd hL base roots).symm.tsum_eq (skelTermW blk D hS L γ δ base roots tt layer selSk
      (modalFnGW Φ hS hSb Fs amp frq))
  refine (e1.symm.trans e2).trans (tsum_congr fun z => ?_)
  have hz : ∀ κs, skelTermW blk D hS L γ δ base roots tt layer selSk (modalFnGW Φ hS hSb Fs amp frq)
      ((Φ.decSplit hS hd hL base roots).symm ⟨z, κs⟩) = (Zw z : ℂ) *
      ∫ q : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))),
        psiIntGW Φ hd D hS hSb L γ δ base Fs layer tt amp frq z κs q := fun κs => hglue ⟨z, κs⟩
  simp_rw [hz]
  rw [tsum_mul_left, fiber_sumGW Φ RB hd D hSb γ δ layer tt amp frq z]

theorem const_splitGW (Φ' : SpliceShape blk Gsb) (hd : Disj blk) (L γ δ : ℝ) :
    (coupling d L γ δ : ℂ) ^ S.order * S.zeta = ((coupling d L γ δ : ℂ) ^ Gsb.order * Gsb.zeta) *
      ∏ j, unitConst (d := d) blk L γ δ j := by
  rw [Φ'.order_split hd, Φ'.zeta_split hd, pow_add]
  unfold unitConst
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

open scoped Classical in
/-- **The per-mode single-state factorization with an arbitrary regional slot family** (cf.
`VineB.SpliceShape.skelVal_modal_eq_outerValM`). -/
theorem skelVal_modal_eq_outerValMGW (RB : RegBoundW blk hS Fs L base) (hd : Disj blk) (hSb : Gsb.IsPlain)
    (hL : L ≠ 0) (γ δ : ℝ) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (selSk : GenDecoration S d roots 0 → Prop) (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (hsum : Summable fun z : GenDecoration Gsb d roots 0 => ampBound hSb L base amp z) :
    skelValW blk D hS L γ δ base roots tt layer selSk (modalFnGW Φ hS hSb Fs amp frq) =
    outerValM Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) (Φ.hinges hd) Zw hSb
      amp frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelMGW blk D hS Fs L γ δ layer base) := by
  have hs := tsum_skelTermGW Φ RB hd hSb hL γ δ D layer tt amp frq selSk Zw hZ hsum
  have hC := const_splitGW (d := d) Φ hd L γ δ
  rw [skelValW_eq, hs, hC]
  unfold outerValM
  simp_rw [outer_term_eqGW Φ hd D hS hSb L γ δ base Fs layer tt amp frq Zw]
  rw [tsum_mul_left]
  ring

end UnitGW

end WaveTurbulence.Flower.MkUnitsL
