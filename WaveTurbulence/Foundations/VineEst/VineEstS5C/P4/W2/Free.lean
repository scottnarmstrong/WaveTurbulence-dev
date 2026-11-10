/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Dict2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.PieceRem
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.AllRows
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Abs
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.WinChain
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RowCont
public import WaveTurbulence.Foundations.VineEst.VineEstS3.LeafChild

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
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
open scoped ENNReal

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- **The free-domain dictionary hypothesis** at the exterior clocks `tt` and the integer boundary `β`. -/
def FreeDict (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (base : Mom d)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ)
    (ψ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ)
    (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    (Mx : CharMix (assemblyShape hM9 B) d) (cr : ClockedRows3 (engDatum hM9 B hG W wN wDec bk cons g g')) : Prop :=
  ∀ x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ), ∀ᵐ τ : (assemblyShape hM9 B).TVar → ℝ,
    recFac (G.sign a.toNode) (G.sign a.toNode) L γ δ tt (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) *
        ψ (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) tt
          (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) =
      Mx.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x *
        (((kind1Pref (D := engDatum hM9 B hG W wN wDec bk cons g g')
            (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) : ℝ) : ℂ) *
          ((engDatum hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2)).indicator
            (fun τ => clockedIntegrand3 cr L γ (2 * δ) η x
              (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) tt τ) τ)

/-- The scalar identity behind `integral_free`. -/
theorem integral_free_aux {α : Type*} [MeasurableSpace α] (μ : Measure α) (S : Set α) (hS : MeasurableSet S) (c m k : ℂ)
    (F f : α → ℂ) (h : ∀ᵐ τ ∂μ, c * F τ = m * (k * S.indicator f τ)) :
    c * ∫ τ, F τ ∂μ = k * (m * ∫ τ in S, f τ ∂μ) := by
  rw [← integral_const_mul, integral_congr_ae h, integral_const_mul, integral_const_mul, integral_indicator hS]
  ring

section Dict
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
  (W : SumintWeightClockData (assemblyShape hM9 B) d) {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (base : Mom d)
  (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ)
  (ψ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ)
  (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
  (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
  (Mx : CharMix (assemblyShape hM9 B) d) (cr : ClockedRows3 (engDatum hM9 B hG W wN wDec bk cons g g'))

/-- The local sum-integral of `ψ` at the integer boundary, in the chain coordinates of the assembly. -/
theorem lkRaw_reindex :
    lkRaw R L base ψ tt (fun j => base + latticePoint L (β j)) =
      ∑' x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ), ∫ τ : (assemblyShape hM9 B).TVar → ℝ,
        ψ (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) tt
          (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) := by
  unfold lkRaw
  rw [← (clNormalizedChainEquiv hL B base β hβ hM9).symm.tsum_eq]
  exact tsum_congr fun x => assemblyClock_integral hM9 B _

/-- The integral of a recentred term over the sumint clocks, under `FreeDict`. -/
theorem integral_free (hD : FreeDict hM9 B hG W hL γ δ η base β hβ tt ψ wN wDec bk cons g g' Mx cr)
    (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)) :
    recFac (G.sign a.toNode) (G.sign a.toNode) L γ δ tt (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) *
        ∫ τ : (assemblyShape hM9 B).TVar → ℝ,
          ψ (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) tt
            (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) =
      ((kind1Pref (D := engDatum hM9 B hG W wN wDec bk cons g g')
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) : ℝ) : ℂ) *
        (Mx.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x *
          ∫ τ in (engDatum hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2),
            clockedIntegrand3 cr L γ (2 * δ) η x (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) tt τ) := by
  exact integral_free_aux (α := (assemblyShape hM9 B).TVar → ℝ) volume _
    (WaveTurbulence.VineEstS3Par.Eng.measurableSet_timeDom (engDatum hM9 B hG W wN wDec bk cons g g') (assemblyShape_I_pos hM9 B)
      (tt 0) (tt 1) (tt 2)) _ _ _ _ _ (hD x)

/-- **`termFnR = c ζ · clockedExprMul3` under the free-domain dictionary.** -/
theorem termFnR_eq_expr3_free (hD : FreeDict hM9 B hG W hL γ δ η base β hβ tt ψ wN wDec bk cons g g' Mx cr) :
    recFac (G.sign a.toNode) (G.sign a.toNode) L γ δ tt
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) *
      ((coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
        lkRaw R L base ψ tt (sumintBoundary (G.sign a.toNode)
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))))) =
      (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
        clockedExprMul3 Mx cr (assemblyShape_I_pos hM9 B) L γ (2 * δ) η tt
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) := by
  rw [sumintBoundary_invol, lkRaw_reindex hM9 B hL base β hβ tt ψ, mul_left_comm, ← tsum_mul_left]
  congr 1
  unfold clockedExprMul3
  rw [← tsum_mul_left]
  refine tsum_congr fun x => ?_
  rw [integral_free hM9 B hG W hL γ δ η base β hβ tt ψ wN wDec bk cons g g' Mx cr hD x]
  rfl

/-- **`ExprAbs ⇒ LkAbs` under the free-domain dictionary.** -/
theorem lkAbs_of_exprAbs_free (hD : FreeDict hM9 B hG W hL γ δ η base β hβ tt ψ wN wDec bk cons g g' Mx cr)
    (hE : ExprAbs Mx cr (assemblyShape_I_pos hM9 B) L γ (2 * δ) η tt
      (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)))) :
    P3.LkAbs R L base ψ tt (sumintBoundary (G.sign a.toNode)
      (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)))) := by
  classical
  rw [sumintBoundary_invol]
  set e := clNormalizedChainEquiv hL B base β hβ hM9 with he
  set E := sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) with hEdef
  set c : ℂ := recFac (G.sign a.toNode) (G.sign a.toNode) L γ δ tt E with hcdef
  have hc0 : c ≠ 0 := Complex.exp_ne_zero _
  set kk : ℂ := ((kind1Pref (D := engDatum hM9 B hG W wN wDec bk cons g g') E : ℝ) : ℂ) with hkk
  set S' := (engDatum hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2) with hS'
  have hS'm : MeasurableSet S' := WaveTurbulence.VineEstS3Par.Eng.measurableSet_timeDom _ _ _ _ _
  have hfun : ∀ x, (fun τ => ψ (clExtendIndices R (e.symm x).1) tt (clLocalClock R tt (assemblyClockEquiv hM9 B τ))) =ᵐ[volume]
      fun τ => c⁻¹ * (Mx.val L E x * (kk * S'.indicator (fun τ => clockedIntegrand3 cr L γ (2 * δ) η x E tt τ) τ)) := by
    intro x
    filter_upwards [hD x] with τ h
    rw [← h, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  refine ⟨fun κ => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ : ∃ x, κ = e.symm x := ⟨e κ, (e.symm_apply_apply κ).symm⟩
    rw [← (assemblyClock_measurePreserving hM9 B).integrable_comp_emb (assemblyClockEquiv hM9 B).measurableEmbedding]
    refine Integrable.congr ?_ (hfun x).symm
    refine Integrable.const_mul (Integrable.const_mul (Integrable.const_mul ?_ _) _) _
    exact (integrable_indicator_iff hS'm).2 (hE.1 x)
  · have hval : ∀ x, ∫ τ : CLInternalTime R, ψ (clExtendIndices R (e.symm x).1) tt (clLocalClock R tt τ) =
        (c⁻¹ * kk) * (Mx.val L E x * ∫ τ in S', clockedIntegrand3 cr L γ (2 * δ) η x E tt τ) := by
      intro x
      rw [assemblyClock_integral hM9 B (fun τ => ψ (clExtendIndices R (e.symm x).1) tt (clLocalClock R tt τ))]
      have h := integral_free hM9 B hG W hL γ δ η base β hβ tt ψ wN wDec bk cons g g' Mx cr hD x
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

/-- **`ExprAbs` for a family of rows given row by row** (the `allRows` analogue of P2's `vineLevel_abs`). -/
theorem allRows_abs {P : WTParams} (hL : 0 < P.L) (hη0 : 0 < P.η) {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I)
    (Mx : CharMix D.S P.d) (hη3 : 3 * P.η ≤ 1) (Cph : ℝ) (hCph0 : 0 ≤ Cph)
    (hCph : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), kind2Factor D P.η τ ≤ Cph)
    (hreg : P.d < D.wDec) (Rw : ∀ ρ : Row D, RowData D (6 * P.η ^ 6) ρ) (hAe : ∀ ρ, (Rw ρ).Ae hI) :
    ∀ tt ∈ outBox D, ∀ E ∈ outSet D P.L P.γ P.η, ExprAbs Mx (allCR Rw) hI P.L P.γ (2 * P.δ) P.η tt E := by
  intro tt htt E hE
  have hθfs : (0 : ℝ) ≤ 6 * P.η ^ 6 := by positivity
  set M := allCM Rw
  have hser := allRows_hser Rw hI hAe
  exact clockedExprMul3_abs Mx (allCR Rw) M.c (fun ρ m => M.S ρ m) (decayWt D D.wDec)
    (fun m v r r' k => M.c_indep v (m (Sum.inr v)) r r' k) hI P.L P.γ (2 * P.δ) P.η hη3 tt E Cph hCph0 (hCph tt htt)
    ((hser tt htt).mono fun τ hs ρ k => hs ρ (E 0 - E 1) k) (fun ρ m => M.S_nonneg ρ m)
    (fun ρ => M.summable_S hθfs ρ) (decayWt_nonneg D D.wDec) (fun ρ m r k => M.norm_le hθfs ρ m r k)
    (summable_decayWt D hL hreg E)

/-- The ambient engine data of a term with every row given (P2's `Amb` without the single-vine ambient rows). -/
structure AmbW (A : ℝ) (P : WTParams) (D : SumintPar.SumintDatum P.d) extends AmbP A P where
  hI : 0 < D.S.I
  Mx : CharMix D.S P.d
  Cph : ℝ
  hCph0 : 0 ≤ Cph
  hCph : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), kind2Factor D P.η τ ≤ Cph
  hreg : P.d < D.wDec
  hAdm : ∀ (p : D.S.TVar → ℝ) (a : D.S.VIdx → Mom P.d → Mom P.d → ℂ) (b : D.S.VIdx → Mom P.d → ℂ),
    WeightBounds D P.L P.γ P.η a b →
      ({ D with param := p, wK := a, wL := b } : SumintPar.SumintDatum P.d).Admissible A P.L P.γ P.η P.D
  hM : D.S.M ≤ P.N 1 ^ 4

/-- The engine prefactor (as `Amb.pre`). -/
noncomputable def AmbW.pre {A : ℝ} {P : WTParams} {D : SumintPar.SumintDatum P.d} (Z : AmbW A P D) : ℝ≥0∞ :=
  (ccη P.η + 1) * ENNReal.ofReal (Z.Mx.mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) *
    sumintRHS0 P D * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ)))

/-- The engine bound of a term with every row given. -/
theorem AmbW.bound {A : ℝ} {P : WTParams} {D : SumintPar.SumintDatum P.d} (Z : AmbW A P D)
    (Rw : ∀ ρ : Row D, RowData D (6 * P.η ^ 6) ρ) (hAe : ∀ ρ, (Rw ρ).Ae Z.hI) :
    XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
        (fun tt E => clockedExprMul3 Z.Mx (allCR Rw) Z.hI P.L P.γ (2 * P.δ) P.η tt E) ≤ Z.pre * ∏ ρ, (Rw ρ).b :=
  allRows_bound Z.hdb Z.hL Z.hη0 Z.hη1 Z.hC1 Z.hδ Z.hd1 Z.hI Z.Mx Z.hη3 Z.Cph Z.hCph0 Z.hCph Z.hreg Z.hAdm Z.hM Rw hAe

section Cert
variable {p : ℕ} {kind : Bool} (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The positive lower child of the bottom joint of the level is a leaf (it carries no clock `t 1`). -/
def LeafPos (lv : Lvl B) : Prop :=
  (lv.c.b.child lv.region.positive).1.2 ∉ (G.tree (lv.c.b.child lv.region.positive).1.1).branching

/-- The negative lower child of the bottom joint of the level is a leaf (it carries no clock `t 2`). -/
def LeafNeg (lv : Lvl B) : Prop :=
  (lv.c.b.child lv.region.negative).1.2 ∉ (G.tree (lv.c.b.child lv.region.negative).1.1).branching

open Classical in
noncomputable instance (lv : Lvl B) : Decidable (LeafPos B lv) := Classical.propDecidable _

open Classical in
noncomputable instance (lv : Lvl B) : Decidable (LeafNeg B lv) := Classical.propDecidable _

/-- **The per-term certificate with every row given** (several operative vines at once).  For a summand `ψ` of the region of the
level `lv`: an assembly `B'` of the region, the engine datum `engDatum hM9 B' hG W wN wDec bk cons g g'` (with the base `κ0.base` and
the output box/set `Bx`, `K`), its ambient engine data `Z`, one `RowData` for every row (its weight is the Fourier sum of its modes, so
the clocked expression is continuous on the cube of output times), the leaf-child independence `hind` of the term (R100 F5: the term
does not see `t 1` / `t 2` when that lower child is a leaf), the free-domain dictionary `FreeDict` at the effective output times
`leafT` of every point of the box and every integer boundary of the output set, and the total size
`traceConst² · pre · ∏ b_ρ ≤ β'` (the trace constant `traceConst² ` pays for the leaf children). -/
def TermCertW {A : ℝ} {P : WTParams} (κ0 : KPar P.d) (lv : Lvl B) (ψ : PsiT G P.d) (Bx : Set (Fin 3 → ℝ))
    (K : Set (Fin 4 → Mom P.d)) (β' : ℝ≥0∞) : Prop :=
  ∃ (n' : ℕ) (hM9 : VINEPARAM) (B' : CLChainAssembly G lv.region n')
    (W : SumintWeightClockData (assemblyShape hM9 B') P.d) (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B').I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B').TVar × (assemblyShape hM9 B').TVar)) (g g' : (assemblyShape hM9 B').VIdx → ℕ)
    (Z : AmbW A P (engDatum hM9 B' hG W wN wDec bk cons g g'))
    (Rw : ∀ ρ : Row (engDatum hM9 B' hG W wN wDec bk cons g g'), RowData (engDatum hM9 B' hG W wN wDec bk cons g g') (6 * P.η ^ 6) ρ)
    (hL : P.L ≠ 0),
    (∀ ρ, (Rw ρ).Ae Z.hI) ∧ (∀ ρ cl r k, (Rw ρ).W cl r k = ∑' m, (Rw ρ).c m r k * WaveTurbulence.VineEstS3.FS.fsPhase m cl) ∧
    W.wBar = κ0.base ∧
    Bx ⊆ outBox (engDatum hM9 B' hG W wN wDec bk cons g g') ∧ K = outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η ∧
    (∀ (t : Fin 3 → ℝ) (β' : Fin 4 → Mom P.d) (κ : CLLocalDecoration lv.region P.L W.wBar β') (u : GBranch G.tree → ℝ),
      u lv.c.a = t 0 → ψ (clExtendIndices lv.region κ.1) t u = ψ (clExtendIndices lv.region κ.1)
        (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut (LeafPos B lv) (LeafNeg B lv) t) u) ∧
    (∀ tt ∈ Bx, ∀ (β : Fin 4 → (Fin P.d → ℤ))
      (hβ : ((G.sign lv.c.a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3),
      sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j)) ∈
        outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η →
      FreeDict hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ
        (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut (LeafPos B lv) (LeafNeg B lv) tt)
        ψ wN wDec bk cons g g' Z.Mx (allCR Rw)) ∧
    Regref.traceConst (r := 3) (2 * P.η ^ 8) WaveTurbulence.VineEstS3.chiUnit ^ 2 * (Z.pre * ∏ ρ, (Rw ρ).b) ≤ β'

variable {A : ℝ} {P : WTParams}

theorem lkRaw_leaf_eq {U' : Finset (GBranch G.tree)} {a' b' : GBranch G.tree} (R' : CLRegionData G U' a' b') (L : ℝ) (base : Mom P.d)
    (ψ : (GNode G.tree → (Fin P.d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ) (t t' : Fin 3 → ℝ) (h0 : t 0 = t' 0)
    (hp : (b'.child R'.positive).1.2 ∉ (G.tree (b'.child R'.positive).1.1).branching ∨ t 1 = t' 1)
    (hn : (b'.child R'.negative).1.2 ∉ (G.tree (b'.child R'.negative).1.1).branching ∨ t 2 = t' 2)
    (hψ : ∀ (β' : Fin 4 → Mom P.d) (κ : CLLocalDecoration R' L base β') (u : GBranch G.tree → ℝ), u a' = t 0 →
      ψ (clExtendIndices R' κ.1) t u = ψ (clExtendIndices R' κ.1) t' u) (β : Fin 4 → Mom P.d) :
    lkRaw R' L base ψ t β = lkRaw R' L base ψ t' β ∧ (LkAbs R' L base ψ t β ↔ LkAbs R' L base ψ t' β) := by
  have hc := WaveTurbulence.VineEstS3.clLocalClock_congr R' t t' h0 hp hn
  have hpt : ∀ (κ : CLLocalDecoration R' L base β) (τ : CLInternalTime R'),
      ψ (clExtendIndices R' κ.1) t (clLocalClock R' t τ) = ψ (clExtendIndices R' κ.1) t' (clLocalClock R' t' τ) := by
    intro κ τ
    rw [hc]
    exact hψ β κ _ (by rw [clLocalClock_upper, h0])
  constructor
  · unfold lkRaw
    exact tsum_congr fun κ => integral_congr_ae (Filter.Eventually.of_forall fun τ => hpt κ τ)
  · unfold LkAbs
    simp only [hpt]

/-- The free-domain identity of a certified term at `tt ∈ Bx` (leaf-adjusted). -/
theorem termFnR_leaf_eq (κ0 : KPar P.d) (hκL : κ0.L = P.L) (hκγ : κ0.γ = P.γ) (hκδ : κ0.δ = P.δ) (lv : Lvl B)
    (ψ : PsiT G P.d) {Bx : Set (Fin 3 → ℝ)} (n' : ℕ) (hM9 : VINEPARAM) (B' : CLChainAssembly G lv.region n')
    (W : SumintWeightClockData (assemblyShape hM9 B') P.d) (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B').I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B').TVar × (assemblyShape hM9 B').TVar)) (g g' : (assemblyShape hM9 B').VIdx → ℕ)
    (Z : AmbW A P (engDatum hM9 B' hG W wN wDec bk cons g g'))
    (Rw : ∀ ρ : Row (engDatum hM9 B' hG W wN wDec bk cons g g'), RowData (engDatum hM9 B' hG W wN wDec bk cons g g') (6 * P.η ^ 6) ρ)
    (hL : P.L ≠ 0) (hbase : W.wBar = κ0.base)
    (hind : ∀ (t : Fin 3 → ℝ) (β' : Fin 4 → Mom P.d) (κ : CLLocalDecoration lv.region P.L W.wBar β') (u : GBranch G.tree → ℝ),
      u lv.c.a = t 0 → ψ (clExtendIndices lv.region κ.1) t u = ψ (clExtendIndices lv.region κ.1)
        (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut (LeafPos B lv) (LeafNeg B lv) t) u)
    (hD : ∀ tt ∈ Bx, ∀ (β : Fin 4 → (Fin P.d → ℤ))
      (hβ : ((G.sign lv.c.a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3),
      sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j)) ∈
        outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η →
      FreeDict hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ
        (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut (LeafPos B lv) (LeafNeg B lv) tt)
        ψ wN wDec bk cons g g' Z.Mx (allCR Rw))
    (s : ℤˣ) (hs : s = G.sign lv.c.a.toNode) (tt : Fin 3 → ℝ) (htt : tt ∈ Bx) (E : Fin 4 → Mom P.d)
    (hE : E ∈ outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η) :
    termFnR B (G.sign lv.c.a.toNode) κ0 lv ψ s tt E =
      Lvl.cst B κ0 lv * clockedExprMul3 Z.Mx (allCR Rw) Z.hI P.L P.γ (2 * P.δ) P.η
        (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut (LeafPos B lv) (LeafNeg B lv) tt) E := by
  subst hs
  set q := (engDatum hM9 B' hG W wN wDec bk cons g g').qOut
  set tt' := WaveTurbulence.VineEstS3.leafT q (LeafPos B lv) (LeafNeg B lv) tt with htt'
  have h0 : tt 0 = tt' 0 := (WaveTurbulence.VineEstS3.leafT_zero q _ _ tt).symm
  have hlk := lkRaw_leaf_eq (P := P) lv.region P.L W.wBar ψ tt tt' h0
    (by by_cases h : LeafPos B lv
        · exact Or.inl h
        · exact Or.inr (by rw [htt', WaveTurbulence.VineEstS3.leafT_one]; simp [h]))
    (by by_cases h : LeafNeg B lv
        · exact Or.inl h
        · exact Or.inr (by rw [htt', WaveTurbulence.VineEstS3.leafT_two]; simp [h]))
    (fun β' κ u hu => hind tt β' κ u hu) (sumintBoundary (G.sign lv.c.a.toNode) E)
  obtain ⟨β, hβ, rfl⟩ := outSet_exists_beta hL (G.sign lv.c.a.toNode) W.wBar E (fun c => (hE.1 c).1) hE.2.1
  have hfd := termFnR_eq_expr3_free hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ tt' ψ wN wDec bk cons g g' Z.Mx (allCR Rw)
    (hD tt htt β hβ hE)
  unfold termFnR termFn Lvl.cst
  rw [hκL, hκγ, hκδ, ← hbase, hlk.1]
  have hrf : recFac (G.sign lv.c.a.toNode) (G.sign lv.c.a.toNode) P.L P.γ P.δ tt
      (sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j))) =
      recFac (G.sign lv.c.a.toNode) (G.sign lv.c.a.toNode) P.L P.γ P.δ tt'
      (sumintBoundary (G.sign lv.c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j))) := by
    unfold recFac; rw [← h0]
  rw [hrf]
  exact hfd

/-- **The term bound from the certificate**: `TermBoundR` of `top_boundR` / `unrolled_boundR_ext` with `β = ‖c ζ‖ β'`. -/
theorem termBoundW (κ0 : KPar P.d) (hκL : κ0.L = P.L) (hκγ : κ0.γ = P.γ) (hκδ : κ0.δ = P.δ) (lv : Lvl B)
    (σ s : ℤˣ) (hσ : σ = G.sign lv.c.a.toNode) (hs : s = σ) {Bx : Set (Fin 3 → ℝ)} {K : Set (Fin 4 → Mom P.d)} {β' : ℝ≥0∞}
    (ψ : PsiT G P.d) (hC : TermCertW (A := A) B hG κ0 lv ψ Bx K β') :
    XNorm00Restr (2 * P.η ^ 8) Bx K (termFnR B σ κ0 lv ψ s) ≤
      ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region‖ₑ * β' := by
  obtain ⟨n', hM9, B', W, wN, wDec, bk, cons, g, g', Z, Rw, hL, hAe, hWs, hbase, hBx, rfl, hind, hD, hβ⟩ := hC
  subst hs hσ
  have hθ : (0 : ℝ) ≤ 2 * P.η ^ 8 := by have := Z.hη0; positivity
  have hcst : Lvl.cst B κ0 lv = (coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region := by
    unfold Lvl.cst; rw [hκL, hκγ, hκδ]
  set Ifun : (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ := fun tt E =>
    Lvl.cst B κ0 lv * clockedExprMul3 Z.Mx (allCR Rw) Z.hI P.L P.γ (2 * P.δ) P.η tt E with hIfun
  have h1 : XNorm00Restr (2 * P.η ^ 8) Bx (outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η) (termFnR B (G.sign lv.c.a.toNode) κ0 lv ψ (G.sign lv.c.a.toNode)) ≤
      XNorm00Restr (2 * P.η ^ 8) Bx (outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η)
        (fun tt E => Ifun (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut (LeafPos B lv) (LeafNeg B lv) tt) E) :=
    XNorm00Restr_mono_of_eq _ _ _ _ _ (fun tt htt E hE =>
      termFnR_leaf_eq B hG κ0 hκL hκγ hκδ lv ψ n' hM9 B' W wN wDec bk cons g g' Z Rw hL hbase hind hD _ rfl tt htt E hE)
  have h2 : XNorm00Restr (2 * P.η ^ 8) Bx (outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η)
        (fun tt E => Ifun (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut (LeafPos B lv) (LeafNeg B lv) tt) E) ≤
      XNorm00Restr (2 * P.η ^ 8) (boxQ (engDatum hM9 B' hG W wN wDec bk cons g g').qOut) (outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η)
        (fun tt E => Ifun (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut (LeafPos B lv) (LeafNeg B lv) tt) E) :=
    XNorm00Restr_mono_set _ hBx _ _
  have hI : ∀ E ∈ outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η, ContinuousOn (fun t => Ifun t E) (WaveTurbulence.VineEstS3.cubeSet (engDatum hM9 B' hG W wN wDec bk cons g g').qOut) :=
    fun E _ => continuousOn_const.mul (expr_continuousOn_cube Z.hL Z.hI Z.Mx Z.hη3 Z.hη0 Z.Cph Z.hCph0 Z.hCph Z.hreg Rw hWs E)
  have h3 := XNorm00Restr_leafQ hθ (engDatum hM9 B' hG W wN wDec bk cons g g').qOut (outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η) Ifun
    (fun tt E => Ifun (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut (LeafPos B lv) (LeafNeg B lv) tt) E)
    (LeafPos B lv) (LeafNeg B lv) hI (fun t _ v _ => rfl)
  have h4 : XNorm00Restr (2 * P.η ^ 8) (boxQ (engDatum hM9 B' hG W wN wDec bk cons g g').qOut) (outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η) Ifun ≤
      ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region‖ₑ *
        XNorm00Restr (2 * P.η ^ 8) (outBox (engDatum hM9 B' hG W wN wDec bk cons g g')) (outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η)
          (fun tt E => clockedExprMul3 Z.Mx (allCR Rw) Z.hI P.L P.γ (2 * P.δ) P.η tt E) := by
    rw [hcst] at hIfun
    have := WaveTurbulence.VineEstS3.Eng.XNorm00Restr_const_mul_le (2 * P.η ^ 8) (outBox (engDatum hM9 B' hG W wN wDec bk cons g g')) (outSet (engDatum hM9 B' hG W wN wDec bk cons g g') P.L P.γ P.η)
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
theorem habsW (κ0 : KPar P.d) (hκL : κ0.L = P.L) (lv : Lvl B) (s : ℤˣ) (hs : s = G.sign lv.c.a.toNode)
    {Bx : Set (Fin 3 → ℝ)} {K : Set (Fin 4 → Mom P.d)} {β' : ℝ≥0∞} (ψ : PsiT G P.d)
    (hC : TermCertW (A := A) B hG κ0 lv ψ Bx K β') :
    ∀ tt ∈ Bx, ∀ E ∈ K, LkAbs lv.region κ0.L κ0.base ψ tt (sumintBoundary s E) := by
  obtain ⟨n', hM9, B', W, wN, wDec, bk, cons, g, g', Z, Rw, hL, hAe, hWs, hbase, hBx, rfl, hind, hD, hβ⟩ := hC
  subst hs
  intro tt htt E hE
  set tt' := WaveTurbulence.VineEstS3.leafT (engDatum hM9 B' hG W wN wDec bk cons g g').qOut (LeafPos B lv) (LeafNeg B lv) tt with htt'
  have hmem : tt' ∈ outBox (engDatum hM9 B' hG W wN wDec bk cons g g') := WaveTurbulence.VineEstS5C.P4.W2.leafT_mem_boxQ (engDatum hM9 B' hG W wN wDec bk cons g g').qOut _ _ (hBx htt)
  have hAbs := allRows_abs Z.hL Z.hη0 (assemblyShape_I_pos hM9 B') Z.Mx Z.hη3 Z.Cph Z.hCph0 Z.hCph Z.hreg Rw hAe tt' hmem E hE
  obtain ⟨β, hβ', rfl⟩ := outSet_exists_beta hL (G.sign lv.c.a.toNode) W.wBar E (fun c => (hE.1 c).1) hE.2.1
  rw [hκL, ← hbase]
  have h0 : tt 0 = tt' 0 := (WaveTurbulence.VineEstS3.leafT_zero (engDatum hM9 B' hG W wN wDec bk cons g g').qOut _ _ tt).symm
  have hlk := lkRaw_leaf_eq (P := P) lv.region P.L W.wBar ψ tt tt' h0
    (by by_cases h : LeafPos B lv
        · exact Or.inl h
        · exact Or.inr (by rw [htt', WaveTurbulence.VineEstS3.leafT_one]; simp [h]))
    (by by_cases h : LeafNeg B lv
        · exact Or.inl h
        · exact Or.inr (by rw [htt', WaveTurbulence.VineEstS3.leafT_two]; simp [h]))
    (fun β' κ u hu => hind tt β' κ u hu) (sumintBoundary (G.sign lv.c.a.toNode) (sumintBoundary (G.sign lv.c.a.toNode)
      (fun j => W.wBar + latticePoint P.L (β j))))
  refine hlk.2.mpr ?_
  exact lkAbs_of_exprAbs_free hM9 B' hG W hL P.γ P.δ P.η W.wBar β hβ' tt' ψ wN wDec bk cons g g' Z.Mx (allCR Rw)
    (hD tt htt β hβ' hE) hAbs

end Cert

end WaveTurbulence.VineEstS5C.P4.W2
