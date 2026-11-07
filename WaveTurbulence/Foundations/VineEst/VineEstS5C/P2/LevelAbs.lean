/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Level
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Abs
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Mink

/-! # P2: absolute convergence and finite sums of level expressions (step 6)

* `ExprAbs`: for every lattice index the integrand is integrable on the time domain and the sum over the lattice of the integrals is
  summable (what linearity needs).
* `vineLevel_abs`: the merged level expression of `vineLevel_bound` satisfies `ExprAbs` for every `tt ∈ outBox D`, `E ∈ outSet D`.
* `clockedExprMul3_finsum`: the finite sum of expressions equals the expression of the summed integrand (Fubini interchange).
* `vineLevel_sum_bound`: finite Minkowski: `XNorm00Restr` of a finite sum of merged level expressions is at most
  `(ccη η + 1) ∑_j (bound of j)`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory Finset
open scoped ENNReal

variable {d : ℕ} {D : SumintPar.SumintDatum d}

/-- Absolute convergence of a clocked expression. -/
def ExprAbs (Mx : CharMix D.S d) (cr : ClockedRows3 D) (hI : 0 < D.S.I) (L γ δ η : ℝ) (tt : Fin 3 → ℝ)
    (E : Fin 4 → Mom d) : Prop :=
  (∀ x : D.S.VIdx → (Fin d → ℤ), Integrable (fun τ => clockedIntegrand3 cr L γ δ η x E tt τ)
      (volume.restrict (D.timeDom hI (tt 0) (tt 1) (tt 2)))) ∧
    Summable fun x : D.S.VIdx → (Fin d → ℤ) => Mx.val L E x * ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2),
      clockedIntegrand3 cr L γ δ η x E tt τ

/-- **The Fubini interchange for a finite sum of row families.** -/
theorem clockedExprMul3_finsum {ι : Type*} (s : Finset ι) (Mx : CharMix D.S d) (cr : ι → ClockedRows3 D)
    (hI : 0 < D.S.I) (L γ δ η : ℝ) (tt : Fin 3 → ℝ) (E : Fin 4 → Mom d)
    (habs : ∀ j ∈ s, ExprAbs Mx (cr j) hI L γ δ η tt E) :
    ∑ j ∈ s, clockedExprMul3 Mx (cr j) hI L γ δ η tt E =
      ((‖E 0 - E 1‖ ^ (Finset.univ.filter fun i => D.S.nor i = false ∧ D.badKind i = 1).card : ℝ) : ℂ) *
        ∑' x : D.S.VIdx → (Fin d → ℤ), Mx.val L E x * ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2),
          ∑ j ∈ s, clockedIntegrand3 (cr j) L γ δ η x E tt τ := by
  unfold clockedExprMul3
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum (fun j hj => (habs j hj).2)]
  congr 1
  refine tsum_congr fun x => ?_
  rw [integral_finsetSum _ (fun j hj => (habs j hj).1 x), Finset.mul_sum]

variable {A : ℝ} {P : WTParams}

/-- **Absolute convergence of the merged level expression.** -/
theorem vineLevel_abs (hL : 0 < P.L) (hη0 : 0 < P.η) {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I)
    (Mx : CharMix D.S P.d) (hη3 : 3 * P.η ≤ 1) (Cph : ℝ) (hCph0 : 0 ≤ Cph)
    (hCph : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), kind2Factor D P.η τ ≤ Cph)
    (hreg : P.d < D.wDec) (cr₀ : ClockedRows3 D) (M₀ : ClockedModes3 D (6 * P.η ^ 6)) (v₀ : D.S.VIdx)
    (K : RowData D (6 * P.η ^ 6) (Sum.inl v₀)) (L : RowData D (6 * P.η ^ 6) (Sum.inr v₀))
    (hK : K.Ae hI) (hLr : L.Ae hI)
    (h0 : ∀ tt ∈ outBox D, ∀ᵐ τ ∂(volume.restrict (D.timeDom hI (tt 0) (tt 1) (tt 2))), ∀ ρ : Row D,
      ρ ≠ Sum.inl v₀ → ρ ≠ Sum.inr v₀ → ∀ r k : Mom P.d,
        HasSum (fun m => M₀.c ρ m r k * fsPhase m (cr₀.clock τ tt ρ)) (cr₀.W ρ (cr₀.clock τ tt ρ) r k)) :
    ∀ tt ∈ outBox D, ∀ E ∈ outSet D P.L P.γ P.η,
      ExprAbs Mx (mergeCR cr₀ v₀ K L) hI P.L P.γ (2 * P.δ) P.η tt E := by
  intro tt htt E hE
  have hθfs : (0 : ℝ) ≤ 6 * P.η ^ 6 := by positivity
  set M := mergeCM M₀ v₀ K L
  have hser := merge_hser cr₀ M₀ v₀ K L hI hK hLr h0
  exact clockedExprMul3_abs Mx (mergeCR cr₀ v₀ K L) M.c (fun ρ m => M.S ρ m) (decayWt D D.wDec)
    (fun m v r r' k => M.c_indep v (m (Sum.inr v)) r r' k) hI P.L P.γ (2 * P.δ) P.η hη3 tt E Cph hCph0 (hCph tt htt)
    ((hser tt htt).mono fun τ hs ρ k => hs ρ (E 0 - E 1) k) (fun ρ m => M.S_nonneg ρ m)
    (fun ρ => M.summable_S hθfs ρ) (decayWt_nonneg D D.wDec) (fun ρ m r k => M.norm_le hθfs ρ m r k)
    (summable_decayWt D hL hreg E)

/-- **Finite Minkowski for merged level expressions.**  Each summand obeys `vineLevel_bound`. -/
theorem vineLevel_sum_bound {ι : Type*} (s : Finset ι) {A : ℝ} {P : WTParams} (hdb : SumintMixParDoubledAt A P)
    (hL : 0 < P.L) (hη0 : 0 < P.η) (hη1 : P.η ≤ 1 / 2) (hC1 : 0 ≤ P.C₁) (hδ : 0 < P.δ) (hd1 : 1 ≤ P.d)
    {D : SumintPar.SumintDatum P.d} (hI : 0 < D.S.I) (Mx : CharMix D.S P.d)
    (hη3 : 3 * P.η ≤ 1) (Cph : ℝ) (hCph0 : 0 ≤ Cph)
    (hCph : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), kind2Factor D P.η τ ≤ Cph)
    (hreg : P.d < D.wDec)
    (hAdm : ∀ (p : D.S.TVar → ℝ) (a : D.S.VIdx → Mom P.d → Mom P.d → ℂ) (b : D.S.VIdx → Mom P.d → ℂ),
      WeightBounds D P.L P.γ P.η a b →
        ({ D with param := p, wK := a, wL := b } : SumintPar.SumintDatum P.d).Admissible A P.L P.γ P.η P.D)
    (hM : D.S.M ≤ P.N 1 ^ 4) (cr₀ : ClockedRows3 D) (M₀ : ClockedModes3 D (6 * P.η ^ 6)) (v₀ : D.S.VIdx)
    (K : ι → RowData D (6 * P.η ^ 6) (Sum.inl v₀)) (L : ι → RowData D (6 * P.η ^ 6) (Sum.inr v₀))
    (hK : ∀ j ∈ s, (K j).Ae hI) (hLr : ∀ j ∈ s, (L j).Ae hI)
    (h0 : ∀ tt ∈ outBox D, ∀ᵐ τ ∂(volume.restrict (D.timeDom hI (tt 0) (tt 1) (tt 2))), ∀ ρ : Row D,
      ρ ≠ Sum.inl v₀ → ρ ≠ Sum.inr v₀ → ∀ r k : Mom P.d,
        HasSum (fun m => M₀.c ρ m r k * fsPhase m (cr₀.clock τ tt ρ)) (cr₀.W ρ (cr₀.clock τ tt ρ) r k)) :
    XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
        (fun tt E => ∑ j ∈ s, clockedExprMul3 Mx (mergeCR cr₀ v₀ (K j) (L j)) hI P.L P.γ (2 * P.δ) P.η tt E) ≤
      (ccη P.η + 1) * ∑ j ∈ s, ((ccη P.η + 1) * ENNReal.ofReal (Mx.mass * (engineConst3 P.η (Fintype.card (Row D)) *
          maxPar D ^ (P.η ^ 6) * sumintRHS0 P D * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
        ((K j).b * (L j).b * ∏ ρ ∈ ((Finset.univ : Finset (Row D)).erase (Sum.inl v₀)).erase (Sum.inr v₀), M₀.b ρ)) := by
  classical
  let : MeasurableSpace s := ⊤
  have : MeasurableSingletonClass s := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hmink := WaveTurbulence.VineEstS3.Mink.XNorm00Restr_tsum_le (ι := s) (θ := 2 * P.η ^ 8) (by positivity)
    (fun c => (D.qOut c : ℝ)) (outBox_subset_cell D) (countable_outSet D P.L P.γ P.η)
    (fun j tt E => clockedExprMul3 Mx (mergeCR cr₀ v₀ (K j) (L j)) hI P.L P.γ (2 * P.δ) P.η tt E)
    (fun tt E => ∑ j ∈ s, clockedExprMul3 Mx (mergeCR cr₀ v₀ (K j) (L j)) hI P.L P.γ (2 * P.δ) P.η tt E)
    (fun tt _ E _ => by
      have := hasSum_fintype (fun j : s => clockedExprMul3 Mx (mergeCR cr₀ v₀ (K j) (L j)) hI P.L P.γ (2 * P.δ) P.η tt E)
      rwa [Finset.sum_coe_sort s (fun j => clockedExprMul3 Mx (mergeCR cr₀ v₀ (K j) (L j)) hI P.L P.γ (2 * P.δ) P.η tt E)]
        at this)
  rw [cc_translate] at hmink
  refine hmink.trans (mul_le_mul' le_rfl ?_)
  rw [tsum_fintype, Finset.sum_coe_sort s (fun j => XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
    (fun tt E => clockedExprMul3 Mx (mergeCR cr₀ v₀ (K j) (L j)) hI P.L P.γ (2 * P.δ) P.η tt E))]
  refine Finset.sum_le_sum fun j hj => ?_
  exact vineLevel_bound hdb hL hη0 hη1 hC1 hδ hd1 hI Mx hη3 Cph hCph0 hCph hreg hAdm hM cr₀ M₀ v₀ (K j) (L j)
    (hK j hj) (hLr j hj) h0

end WaveTurbulence.VineEstS5C.P2
