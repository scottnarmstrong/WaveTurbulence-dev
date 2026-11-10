/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.AllRows
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Abs
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.WinChain
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RowCont
public import WaveTurbulence.Foundations.VineEst.VineEstS3.LeafChild
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.Free
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P2.Dict2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.WinChain
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.Free` (sha256 d08bd88808bfaa24…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2: the free-domain dictionary (design point W2-D1) and the per-term certificate of several operative vines

**Design point W2-D1 (time domain).**  P2's dictionary (`TermData.hψ`, `DictHyp.hsub`) asks every term to be a generic summand
`clLocalSummandGen R Φ` of the region, i.e. supported in the *native* clock domain of `R`.  That is false for the pieces whose clause
is the twin's order: for a II-a start state (`νA = 1`, native `t₀ < t₁`) the piece (a) II-b `1_{t₁ ≤ t₀ < s₁}` and the remainder rows
`remB` (`1_{t₀ < s₁}`) live outside it (symmetrically for `νA = -1`), because the frame `spartFrame` drops the parent-clock
condition at the lower joint (`DomF`).  TARGET (sumint) allows any order constraints in `𝒟` (L1612 (iii)); the engine datum of such a
piece has constraints `native ∖ {(t₀, t₁)} ∪ {(t₁,t₀), (t₀,s₁)}`, which is not a subset of the native domain.  So the dictionary is
restated without the native domain:

* `FreeDict`: for every lattice point `x` of the chain coordinates and a.e. clock `τ` of the sumint shape, the recentred term at the
  reindexed decoration and clock is `Mx.val · kind1Pref · 1_{timeDom} · clockedIntegrand3` of the engine datum (any constraints,
  any parameters; the R58 modulation `e^{πiλτ_b}` is the parameter `λ` of the clock of `b`).
* `termFnR_eq_expr3_free`, `lkAbs_of_exprAbs_free`, `recBound_free`: P2's `termFnR_eq_expr3`, `lkAbs_of_exprAbs`, `recBound_of_engine`
  under `FreeDict` (no `RowFactorizationR`, no `hψ`, no `hsub`/`hvan`, no `hpar`/`hbad`).
* `allRows_abs`: `ExprAbs` for a family of rows given row by row (`allCR`, P4/AllRows).
* `AmbW`, `TermCertW`, **`termBoundW`**, **`habsW`**: the per-term certificate with every row given (several operative vines at
  once) and its two consequences in exactly the form of `top_boundR`'s `TermBoundR` and `habs`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
variable {γF : ℝ}
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.GammaLow.Famb.VineEstS2
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS4
open scoped ENNReal

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- **The free-domain dictionary hypothesis** at the exterior clocks `tt` and the integer boundary `β`. -/
def FreeDictΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (base : Mom d)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ)
    (ψ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ)
    (wN wDec : ℕ) (bk : Fin (assemblyShapeΓ hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) (g g' : (assemblyShapeΓ hM9 B).VIdx → ℕ)
    (Mx : CharMix (assemblyShapeΓ hM9 B) d) (cr : ClockedRows3 (engDatumΓ hM9 B hG W wN wDec bk cons g g')) : Prop :=
  ∀ x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ), ∀ᵐ τ : (assemblyShapeΓ hM9 B).TVar → ℝ,
    recFac (G.sign a.toNode) (G.sign a.toNode) L γ δ tt (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) *
        ψ (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1) tt
          (clLocalClock R tt (assemblyClockEquivΓ hM9 B τ)) =
      Mx.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x *
        (((kind1Pref (D := engDatumΓ hM9 B hG W wN wDec bk cons g g')
            (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) : ℝ) : ℂ) *
          ((engDatumΓ hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_posΓ hM9 B) (tt 0) (tt 1) (tt 2)).indicator
            (fun τ => clockedIntegrand3 cr L γ (2 * δ) η x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) tt τ) τ)

section Dict
variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
  (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (base : Mom d)
  (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ)
  (ψ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ)
  (wN wDec : ℕ) (bk : Fin (assemblyShapeΓ hM9 B).I → Fin 4)
  (cons : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) (g g' : (assemblyShapeΓ hM9 B).VIdx → ℕ)
  (Mx : CharMix (assemblyShapeΓ hM9 B) d) (cr : ClockedRows3 (engDatumΓ hM9 B hG W wN wDec bk cons g g'))

/-- The local sum-integral of `ψ` at the integer boundary, in the chain coordinates of the assembly. -/
theorem lkRaw_reindexΓ :
    lkRaw R L base ψ tt (fun j => base + latticePoint L (β j)) =
      ∑' x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ), ∫ τ : (assemblyShapeΓ hM9 B).TVar → ℝ,
        ψ (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1) tt
          (clLocalClock R tt (assemblyClockEquivΓ hM9 B τ)) := by
  unfold lkRaw
  rw [← (clNormalizedChainEquivΓ hL B base β hβ hM9).symm.tsum_eq]
  exact tsum_congr fun x => assemblyClock_integralΓ hM9 B _

/-- The integral of a recentred term over the sumint clocks, under `FreeDict`. -/
theorem integral_freeΓ (hD : FreeDictΓ hM9 B hG W hL γ δ η base β hβ tt ψ wN wDec bk cons g g' Mx cr)
    (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) :
    recFac (G.sign a.toNode) (G.sign a.toNode) L γ δ tt (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) *
        ∫ τ : (assemblyShapeΓ hM9 B).TVar → ℝ,
          ψ (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1) tt
            (clLocalClock R tt (assemblyClockEquivΓ hM9 B τ)) =
      ((kind1Pref (D := engDatumΓ hM9 B hG W wN wDec bk cons g g')
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) : ℝ) : ℂ) *
        (Mx.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x *
          ∫ τ in (engDatumΓ hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_posΓ hM9 B) (tt 0) (tt 1) (tt 2),
            clockedIntegrand3 cr L γ (2 * δ) η x (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) tt τ) := by
  exact integral_free_aux (α := (assemblyShapeΓ hM9 B).TVar → ℝ) volume _
    (WaveTurbulence.VineEstS3Par.Eng.measurableSet_timeDom (engDatumΓ hM9 B hG W wN wDec bk cons g g') (assemblyShape_I_posΓ hM9 B)
      (tt 0) (tt 1) (tt 2)) _ _ _ _ _ (hD x)

/-- **`termFnR = c ζ · clockedExprMul3` under the free-domain dictionary.** -/
theorem termFnR_eq_expr3_freeΓ (hD : FreeDictΓ hM9 B hG W hL γ δ η base β hβ tt ψ wN wDec bk cons g g' Mx cr) :
    recFac (G.sign a.toNode) (G.sign a.toNode) L γ δ tt
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) *
      ((coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
        lkRaw R L base ψ tt (sumintBoundary (G.sign a.toNode)
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))))) =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
        clockedExprMul3 Mx cr (assemblyShape_I_posΓ hM9 B) L γ (2 * δ) η tt
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) := by
  rw [sumintBoundary_invol, lkRaw_reindexΓ hM9 B hL base β hβ tt ψ, mul_left_comm, ← tsum_mul_left]
  congr 1
  unfold clockedExprMul3
  rw [← tsum_mul_left]
  refine tsum_congr fun x => ?_
  rw [integral_freeΓ hM9 B hG W hL γ δ η base β hβ tt ψ wN wDec bk cons g g' Mx cr hD x]
  rfl

/-- **`ExprAbs ⇒ LkAbs` under the free-domain dictionary.** -/
theorem lkAbs_of_exprAbs_freeΓ (hD : FreeDictΓ hM9 B hG W hL γ δ η base β hβ tt ψ wN wDec bk cons g g' Mx cr)
    (hE : ExprAbs Mx cr (assemblyShape_I_posΓ hM9 B) L γ (2 * δ) η tt
      (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)))) :
    P3.LkAbs R L base ψ tt (sumintBoundary (G.sign a.toNode)
      (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)))) := by
  classical
  rw [sumintBoundary_invol]
  set e := clNormalizedChainEquivΓ hL B base β hβ hM9 with he
  set E := sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) with hEdef
  set c : ℂ := recFac (G.sign a.toNode) (G.sign a.toNode) L γ δ tt E with hcdef
  have hc0 : c ≠ 0 := Complex.exp_ne_zero _
  set kk : ℂ := ((kind1Pref (D := engDatumΓ hM9 B hG W wN wDec bk cons g g') E : ℝ) : ℂ) with hkk
  set S' := (engDatumΓ hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_posΓ hM9 B) (tt 0) (tt 1) (tt 2) with hS'
  have hS'm : MeasurableSet S' := WaveTurbulence.VineEstS3Par.Eng.measurableSet_timeDom _ _ _ _ _
  have hfun : ∀ x, (fun τ => ψ (clExtendIndices R (e.symm x).1) tt (clLocalClock R tt (assemblyClockEquivΓ hM9 B τ))) =ᵐ[volume]
      fun τ => c⁻¹ * (Mx.val L E x * (kk * S'.indicator (fun τ => clockedIntegrand3 cr L γ (2 * δ) η x E tt τ) τ)) := by
    intro x
    filter_upwards [hD x] with τ h
    rw [← h, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  refine ⟨fun κ => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ : ∃ x, κ = e.symm x := ⟨e κ, (e.symm_apply_apply κ).symm⟩
    rw [← (assemblyClock_measurePreservingΓ hM9 B).integrable_comp_emb (assemblyClockEquivΓ hM9 B).measurableEmbedding]
    refine Integrable.congr ?_ (hfun x).symm
    refine Integrable.const_mul (Integrable.const_mul (Integrable.const_mul ?_ _) _) _
    exact (integrable_indicator_iff hS'm).2 (hE.1 x)
  · have hval : ∀ x, ∫ τ : CLInternalTime R, ψ (clExtendIndices R (e.symm x).1) tt (clLocalClock R tt τ) =
        (c⁻¹ * kk) * (Mx.val L E x * ∫ τ in S', clockedIntegrand3 cr L γ (2 * δ) η x E tt τ) := by
      intro x
      rw [assemblyClock_integralΓ hM9 B (fun τ => ψ (clExtendIndices R (e.symm x).1) tt (clLocalClock R tt τ))]
      have h := integral_freeΓ hM9 B hG W hL γ δ η base β hβ tt ψ wN wDec bk cons g g' Mx cr hD x
      rw [← hEdef, ← hcdef, ← hkk, ← hS'] at h
      have h' := congrArg (fun z => c⁻¹ * z) h
      simp only at h'
      rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul] at h'
      rw [h']
      ring
    have : Summable fun x => ∫ τ : CLInternalTime R, ψ (clExtendIndices R (e.symm x).1) tt (clLocalClock R tt τ) :=
      (hE.2.mul_left (c⁻¹ * kk)).congr fun x => (hval x).symm
    exact (Equiv.summable_iff e.symm).1 this

end Dict

section Cert
variable {p : ℕ} {kind : Bool} (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The positive lower child of the bottom joint of the level is a leaf (it carries no clock `t 1`). -/
def LeafPosΓ (lv : LvlΓ B) : Prop :=
  (lv.c.b.child lv.region.positive).1.2 ∉ (G.tree (lv.c.b.child lv.region.positive).1.1).branching

/-- The negative lower child of the bottom joint of the level is a leaf (it carries no clock `t 2`). -/
def LeafNegΓ (lv : LvlΓ B) : Prop :=
  (lv.c.b.child lv.region.negative).1.2 ∉ (G.tree (lv.c.b.child lv.region.negative).1.1).branching

open Classical in
noncomputable instance (lv : LvlΓ B) : Decidable (LeafPosΓ B lv) := Classical.propDecidable _

open Classical in
noncomputable instance (lv : LvlΓ B) : Decidable (LeafNegΓ B lv) := Classical.propDecidable _

/-- **The per-term certificate with every row given** (several operative vines at once).  For a summand `ψ` of the region of the
level `lv`: an assembly `B'` of the region, the engine datum `engDatum hM9 B' hG W wN wDec bk cons g g'` (with the base `κ0.base` and
the output box/set `Bx`, `K`), its ambient engine data `Z`, one `RowData` for every row (its weight is the Fourier sum of its modes, so
the clocked expression is continuous on the cube of output times), the leaf-child independence `hind` of the term (R100 F5: the term
does not see `t 1` / `t 2` when that lower child is a leaf), the free-domain dictionary `FreeDict` at the effective output times
`leafT` of every point of the box and every integer boundary of the output set, and the total size
`traceConst² · pre · ∏ b_ρ ≤ β'` (the trace constant `traceConst² ` pays for the leaf children). -/
def TermCertWΓ {A : ℝ} {P : WTParams} (κ0 : KPar P.d) (lv : LvlΓ B) (ψ : PsiT G P.d) (Bx : Set (Fin 3 → ℝ))
    (K : Set (Fin 4 → Mom P.d)) (β' : ℝ≥0∞) : Prop :=
  ∃ (n' : ℕ) (hM9 : NormalChartSupply γF) (B' : CLChainAssemblyΓ γF G lv.region n')
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B') P.d) (wN wDec : ℕ) (bk : Fin (assemblyShapeΓ hM9 B').I → Fin 4)
    (cons : Finset ((assemblyShapeΓ hM9 B').TVar × (assemblyShapeΓ hM9 B').TVar)) (g g' : (assemblyShapeΓ hM9 B').VIdx → ℕ)
    (Z : AmbW A P (engDatumΓ hM9 B' hG W wN wDec bk cons g g'))
    (Rw : ∀ ρ : Row (engDatumΓ hM9 B' hG W wN wDec bk cons g g'), RowData (engDatumΓ hM9 B' hG W wN wDec bk cons g g') (6 * P.η ^ 6) ρ)
    (hL : P.L ≠ 0),
    (∀ ρ, (Rw ρ).Ae Z.hI) ∧ (∀ ρ cl r k, (Rw ρ).W cl r k = ∑' m, (Rw ρ).c m r k * WaveTurbulence.VineEstS3.FS.fsPhase m cl) ∧
    W.wBar = κ0.base ∧
    Bx ⊆ outBox (engDatumΓ hM9 B' hG W wN wDec bk cons g g') ∧ K = outSet (engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η ∧
    (∀ (t : Fin 3 → ℝ) (β' : Fin 4 → Mom P.d) (κ : CLLocalDecoration lv.region P.L W.wBar β') (u : GBranch G.tree → ℝ),
      u lv.c.a = t 0 → ψ (clExtendIndices lv.region κ.1) t u = ψ (clExtendIndices lv.region κ.1)
        (WaveTurbulence.VineEstS3.leafT (engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut (LeafPosΓ B lv) (LeafNegΓ B lv) t) u) ∧
    (∀ tt ∈ Bx, ∀ (β : Fin 4 → (Fin P.d → ℤ))
      (hβ : ((G.sign lv.c.a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3),
      sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j)) ∈
        outSet (engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η →
      FreeDictΓ hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ
        (WaveTurbulence.VineEstS3.leafT (engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut (LeafPosΓ B lv) (LeafNegΓ B lv) tt)
        ψ wN wDec bk cons g g' Z.Mx (allCR Rw)) ∧
    Regref.traceConst (r := 3) (2 * P.η ^ 8) WaveTurbulence.VineEstS3.chiUnit ^ 2 * (Z.pre * ∏ ρ, (Rw ρ).b) ≤ β'

variable {A : ℝ} {P : WTParams}

/-- The free-domain identity of a certified term at `tt ∈ Bx` (leaf-adjusted). -/
theorem termFnR_leaf_eqΓ (κ0 : KPar P.d) (hκL : κ0.L = P.L) (hκγ : κ0.γ = P.γ) (hκδ : κ0.δ = P.δ) (lv : LvlΓ B)
    (ψ : PsiT G P.d) {Bx : Set (Fin 3 → ℝ)} (n' : ℕ) (hM9 : NormalChartSupply γF) (B' : CLChainAssemblyΓ γF G lv.region n')
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B') P.d) (wN wDec : ℕ) (bk : Fin (assemblyShapeΓ hM9 B').I → Fin 4)
    (cons : Finset ((assemblyShapeΓ hM9 B').TVar × (assemblyShapeΓ hM9 B').TVar)) (g g' : (assemblyShapeΓ hM9 B').VIdx → ℕ)
    (Z : AmbW A P (engDatumΓ hM9 B' hG W wN wDec bk cons g g'))
    (Rw : ∀ ρ : Row (engDatumΓ hM9 B' hG W wN wDec bk cons g g'), RowData (engDatumΓ hM9 B' hG W wN wDec bk cons g g') (6 * P.η ^ 6) ρ)
    (hL : P.L ≠ 0) (hbase : W.wBar = κ0.base)
    (hind : ∀ (t : Fin 3 → ℝ) (β' : Fin 4 → Mom P.d) (κ : CLLocalDecoration lv.region P.L W.wBar β') (u : GBranch G.tree → ℝ),
      u lv.c.a = t 0 → ψ (clExtendIndices lv.region κ.1) t u = ψ (clExtendIndices lv.region κ.1)
        (WaveTurbulence.VineEstS3.leafT (engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut (LeafPosΓ B lv) (LeafNegΓ B lv) t) u)
    (hD : ∀ tt ∈ Bx, ∀ (β : Fin 4 → (Fin P.d → ℤ))
      (hβ : ((G.sign lv.c.a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3),
      sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j)) ∈
        outSet (engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η →
      FreeDictΓ hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ
        (WaveTurbulence.VineEstS3.leafT (engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut (LeafPosΓ B lv) (LeafNegΓ B lv) tt)
        ψ wN wDec bk cons g g' Z.Mx (allCR Rw))
    (s : ℤˣ) (hs : s = G.sign lv.c.a.toNode) (tt : Fin 3 → ℝ) (htt : tt ∈ Bx) (E : Fin 4 → Mom P.d)
    (hE : E ∈ outSet (engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η) :
    termFnRΓ B (G.sign lv.c.a.toNode) κ0 lv ψ s tt E =
      LvlΓ.cstΓ B κ0 lv * clockedExprMul3 Z.Mx (allCR Rw) Z.hI P.L P.γ (2 * P.δ) P.η
        (WaveTurbulence.VineEstS3.leafT (engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut (LeafPosΓ B lv) (LeafNegΓ B lv) tt) E := by
  subst hs
  set q := (engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut
  set tt' := WaveTurbulence.VineEstS3.leafT q (LeafPosΓ B lv) (LeafNegΓ B lv) tt with htt'
  have h0 : tt 0 = tt' 0 := (WaveTurbulence.VineEstS3.leafT_zero q _ _ tt).symm
  have hlk := lkRaw_leaf_eq (P := P) lv.region P.L W.wBar ψ tt tt' h0
    (by by_cases h : LeafPosΓ B lv
        · exact Or.inl h
        · exact Or.inr (by rw [htt', WaveTurbulence.VineEstS3.leafT_one]; simp [h]))
    (by by_cases h : LeafNegΓ B lv
        · exact Or.inl h
        · exact Or.inr (by rw [htt', WaveTurbulence.VineEstS3.leafT_two]; simp [h]))
    (fun β' κ u hu => hind tt β' κ u hu) (sumintBoundary (G.sign lv.c.a.toNode) E)
  obtain ⟨β, hβ, rfl⟩ := outSet_exists_beta hL (G.sign lv.c.a.toNode) W.wBar E (fun c => (hE.1 c).1) hE.2.1
  have hfd := termFnR_eq_expr3_freeΓ hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ tt' ψ wN wDec bk cons g g' Z.Mx (allCR Rw)
    (hD tt htt β hβ hE)
  unfold termFnRΓ termFnΓ LvlΓ.cstΓ
  rw [hκL, hκγ, hκδ, ← hbase, hlk.1]
  have hrf : recFac (G.sign lv.c.a.toNode) (G.sign lv.c.a.toNode) P.L P.γ P.δ tt
      (sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j))) =
      recFac (G.sign lv.c.a.toNode) (G.sign lv.c.a.toNode) P.L P.γ P.δ tt'
      (sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j))) := by
    unfold recFac; rw [← h0]
  rw [hrf]
  exact hfd

/-- **The term bound from the certificate**: `TermBoundR` of `top_boundR` / `unrolled_boundR_ext` with `β = ‖c ζ‖ β'`. -/
theorem termBoundWΓ (κ0 : KPar P.d) (hκL : κ0.L = P.L) (hκγ : κ0.γ = P.γ) (hκδ : κ0.δ = P.δ) (lv : LvlΓ B)
    (σ s : ℤˣ) (hσ : σ = G.sign lv.c.a.toNode) (hs : s = σ) {Bx : Set (Fin 3 → ℝ)} {K : Set (Fin 4 → Mom P.d)} {β' : ℝ≥0∞}
    (ψ : PsiT G P.d) (hC : TermCertWΓ (A := A) B hG κ0 lv ψ Bx K β') :
    XNorm00Restr (2 * P.η ^ 8) Bx K (termFnRΓ B σ κ0 lv ψ s) ≤
      ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region‖ₑ * β' := by
  obtain ⟨n', hM9, B', W, wN, wDec, bk, cons, g, g', Z, Rw, hL, hAe, hWs, hbase, hBx, rfl, hind, hD, hβ⟩ := hC
  subst hs hσ
  have hθ : (0 : ℝ) ≤ 2 * P.η ^ 8 := by have := Z.hη0; positivity
  have hcst : LvlΓ.cstΓ B κ0 lv = (coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region := by
    unfold LvlΓ.cstΓ; rw [hκL, hκγ, hκδ]
  set Ifun : (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ := fun tt E =>
    LvlΓ.cstΓ B κ0 lv * clockedExprMul3 Z.Mx (allCR Rw) Z.hI P.L P.γ (2 * P.δ) P.η tt E with hIfun
  have h1 : XNorm00Restr (2 * P.η ^ 8) Bx (outSet (engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η) (termFnRΓ B (G.sign lv.c.a.toNode) κ0 lv ψ (G.sign lv.c.a.toNode)) ≤
      XNorm00Restr (2 * P.η ^ 8) Bx (outSet (engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η)
        (fun tt E => Ifun (WaveTurbulence.VineEstS3.leafT (engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut (LeafPosΓ B lv) (LeafNegΓ B lv) tt) E) :=
    XNorm00Restr_mono_of_eq _ _ _ _ _ (fun tt htt E hE =>
      termFnR_leaf_eqΓ B hG κ0 hκL hκγ hκδ lv ψ n' hM9 B' W wN wDec bk cons g g' Z Rw hL hbase hind hD _ rfl tt htt E hE)
  have h2 : XNorm00Restr (2 * P.η ^ 8) Bx (outSet (engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η)
        (fun tt E => Ifun (WaveTurbulence.VineEstS3.leafT (engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut (LeafPosΓ B lv) (LeafNegΓ B lv) tt) E) ≤
      XNorm00Restr (2 * P.η ^ 8) (boxQ (engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut) (outSet (engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η)
        (fun tt E => Ifun (WaveTurbulence.VineEstS3.leafT (engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut (LeafPosΓ B lv) (LeafNegΓ B lv) tt) E) :=
    XNorm00Restr_mono_set _ hBx _ _
  have hI : ∀ E ∈ outSet (engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η, ContinuousOn (fun t => Ifun t E) (WaveTurbulence.VineEstS3.cubeSet (engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut) :=
    fun E _ => continuousOn_const.mul (expr_continuousOn_cube Z.hL Z.hI Z.Mx Z.hη3 Z.hη0 Z.Cph Z.hCph0 Z.hCph Z.hreg Rw hWs E)
  have h3 := XNorm00Restr_leafQ hθ (engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut (outSet (engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η) Ifun
    (fun tt E => Ifun (WaveTurbulence.VineEstS3.leafT (engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut (LeafPosΓ B lv) (LeafNegΓ B lv) tt) E)
    (LeafPosΓ B lv) (LeafNegΓ B lv) hI (fun t _ v _ => rfl)
  have h4 : XNorm00Restr (2 * P.η ^ 8) (boxQ (engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut) (outSet (engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η) Ifun ≤
      ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region‖ₑ *
        XNorm00Restr (2 * P.η ^ 8) (outBox (engDatumΓ hM9 B' hG W wN wDec bk cons g g')) (outSet (engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η)
          (fun tt E => clockedExprMul3 Z.Mx (allCR Rw) Z.hI P.L P.γ (2 * P.δ) P.η tt E) := by
    rw [hcst] at hIfun
    have := WaveTurbulence.VineEstS3.Eng.XNorm00Restr_const_mul_le (2 * P.η ^ 8) (outBox (engDatumΓ hM9 B' hG W wN wDec bk cons g g')) (outSet (engDatumΓ hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η)
      ((coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region)
      (fun tt E => clockedExprMul3 Z.Mx (allCR Rw) Z.hI P.L P.γ (2 * P.δ) P.η tt E)
    simpa [hIfun, hcst, outBoxPar_eq] using this
  have h5 := Z.bound Rw hAe
  calc _ ≤ _ := h1.trans (h2.trans h3)
    _ ≤ Regref.traceConst (r := 3) (2 * P.η ^ 8) WaveTurbulence.VineEstS3.chiUnit ^ 2 *
        (‖(coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region‖ₑ * (Z.pre * ∏ ρ, (Rw ρ).b)) :=
      mul_le_mul' le_rfl (h4.trans (mul_le_mul' le_rfl h5))
    _ = ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region‖ₑ *
        (Regref.traceConst (r := 3) (2 * P.η ^ 8) WaveTurbulence.VineEstS3.chiUnit ^ 2 * (Z.pre * ∏ ρ, (Rw ρ).b)) := by ring
    _ ≤ _ := mul_le_mul' le_rfl hβ

/-- **Absolute convergence of the term from the certificate** (`habs` of `top_boundR`). -/
theorem habsWΓ (κ0 : KPar P.d) (hκL : κ0.L = P.L) (lv : LvlΓ B) (s : ℤˣ) (hs : s = G.sign lv.c.a.toNode)
    {Bx : Set (Fin 3 → ℝ)} {K : Set (Fin 4 → Mom P.d)} {β' : ℝ≥0∞} (ψ : PsiT G P.d)
    (hC : TermCertWΓ (A := A) B hG κ0 lv ψ Bx K β') :
    ∀ tt ∈ Bx, ∀ E ∈ K, LkAbs lv.region κ0.L κ0.base ψ tt (sumintBoundary s E) := by
  obtain ⟨n', hM9, B', W, wN, wDec, bk, cons, g, g', Z, Rw, hL, hAe, hWs, hbase, hBx, rfl, hind, hD, hβ⟩ := hC
  subst hs
  intro tt htt E hE
  set tt' := WaveTurbulence.VineEstS3.leafT (engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut (LeafPosΓ B lv) (LeafNegΓ B lv) tt with htt'
  have hmem : tt' ∈ outBox (engDatumΓ hM9 B' hG W wN wDec bk cons g g') := WaveTurbulence.VineEstS5C.P4.W2.leafT_mem_boxQ (engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut _ _ (hBx htt)
  have hAbs := allRows_abs Z.hL Z.hη0 (assemblyShape_I_posΓ hM9 B') Z.Mx Z.hη3 Z.Cph Z.hCph0 Z.hCph Z.hreg Rw hAe tt' hmem E hE
  obtain ⟨β, hβ', rfl⟩ := outSet_exists_beta hL (G.sign lv.c.a.toNode) W.wBar E (fun c => (hE.1 c).1) hE.2.1
  rw [hκL, ← hbase]
  have h0 : tt 0 = tt' 0 := (WaveTurbulence.VineEstS3.leafT_zero (engDatumΓ hM9 B' hG W wN wDec bk cons g g').qOut _ _ tt).symm
  have hlk := lkRaw_leaf_eq (P := P) lv.region P.L W.wBar ψ tt tt' h0
    (by by_cases h : LeafPosΓ B lv
        · exact Or.inl h
        · exact Or.inr (by rw [htt', WaveTurbulence.VineEstS3.leafT_one]; simp [h]))
    (by by_cases h : LeafNegΓ B lv
        · exact Or.inl h
        · exact Or.inr (by rw [htt', WaveTurbulence.VineEstS3.leafT_two]; simp [h]))
    (fun β' κ u hu => hind tt β' κ u hu) (sumintBoundary (G.sign lv.c.a.toNode) (sumintBoundary (G.sign lv.c.a.toNode)
      (fun j => W.wBar + latticePoint P.L (β j))))
  refine hlk.2.mpr ?_
  exact lkAbs_of_exprAbs_freeΓ hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ' tt' ψ wN wDec bk cons g g' Z.Mx (allCR Rw)
    (hD tt htt β hβ' hE) hAbs

end Cert

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
