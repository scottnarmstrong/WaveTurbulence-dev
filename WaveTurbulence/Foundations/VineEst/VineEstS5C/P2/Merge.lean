/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Engine
public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Rows

/-! # P2: the engine datum of one operative vine level (V5 Step 4d part C, packet P2)

`RowData D θ ρ`: everything the arity-3 engine `clockedBoundMix3` asks of ONE weight row `ρ` (weight, three clock
slots, Fourier modes, mode size, a.e. expansion).  `mergeRows`: replace the two rows `𝒦 = inl v₀`, `ℒ = inr v₀` of the vine
`v₀` in an ambient family `(cr₀, M₀)` by two `RowData`.  **`vineLevel_bound`**: the `XNorm00Restr` bound of the merged
clocked expression, with the product of the mode sizes split as `b_𝒦 b_ℒ ∏_{other rows} b`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory Finset
open scoped ENNReal

variable {d : ℕ} {D : SumintPar.SumintDatum d}

/-- The engine data of one weight row `ρ`: weight, slots, mode coefficients, mode size.  `indep`: an `ℒ` row does not
depend on `r` (weight and coefficients). -/
structure RowData (D : SumintPar.SumintDatum d) (θ : ℝ) (ρ : Row D) where
  W : (Fin 3 → ℝ) → Mom d → Mom d → ℂ
  slot : Fin 3 → VineEstS3Par.Eng.Slot D
  c : (Fin 3 → ℤ) → Mom d → Mom d → ℂ
  b : ℝ≥0∞
  b_ne_top : b ≠ ⊤
  fs : coefBound θ D.wN (rowOrder D ρ) c ≤ b
  indepW : ∀ v, ρ = Sum.inr v → ∀ (c : Fin 3 → ℝ) (r r' k : Mom d), W c r k = W c r' k
  indepC : ∀ v, ρ = Sum.inr v → ∀ (m : Fin 3 → ℤ) (r r' k : Mom d), c m r k = c m r' k

/-- The clock triple of a row datum at internal times `τ` and external times `tt`. -/
def RowData.clk {θ : ℝ} {ρ : Row D} (R : RowData D θ ρ) (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => slotVal D τ tt (R.slot i)

/-- The a.e. mode expansion of a row datum on the time domain (the form of `hser` of the engine, for one row). -/
def RowData.Ae {θ : ℝ} {ρ : Row D} (R : RowData D θ ρ) (hI : 0 < D.S.I) : Prop :=
  ∀ tt ∈ outBox D, ∀ᵐ τ ∂(volume.restrict (D.timeDom hI (tt 0) (tt 1) (tt 2))), ∀ r k : Mom d,
    HasSum (fun m => R.c m r k * fsPhase m (R.clk τ tt)) (R.W (R.clk τ tt) r k)

section Merge
open Classical

variable {θ : ℝ}

/-- The clocked weights of `cr₀` with the two rows of the vine `v₀` replaced. -/
noncomputable def mergeCR (cr₀ : ClockedRows3 D) (v₀ : D.S.VIdx) (K : RowData D θ (Sum.inl v₀))
    (L : RowData D θ (Sum.inr v₀)) : ClockedRows3 D where
  W := fun ρ => if ρ = Sum.inl v₀ then K.W else if ρ = Sum.inr v₀ then L.W else cr₀.W ρ
  slot := fun ρ => if ρ = Sum.inl v₀ then K.slot else if ρ = Sum.inr v₀ then L.slot else cr₀.slot ρ
  W_indep := by
    intro v c r r' k
    by_cases h1 : (Sum.inr v : Row D) = Sum.inl v₀
    · exact absurd h1 (by simp)
    by_cases h2 : (Sum.inr v : Row D) = Sum.inr v₀
    · simp only [h1, h2, ite_false, ite_true]
      exact L.indepW v₀ rfl c r r' k
    · simp only [h1, h2, ite_false]
      exact cr₀.W_indep v c r r' k

/-- The mode families of `M₀` with the two rows of the vine `v₀` replaced. -/
noncomputable def mergeCM (M₀ : ClockedModes3 D θ) (v₀ : D.S.VIdx) (K : RowData D θ (Sum.inl v₀))
    (L : RowData D θ (Sum.inr v₀)) : ClockedModes3 D θ where
  c := fun ρ => if ρ = Sum.inl v₀ then K.c else if ρ = Sum.inr v₀ then L.c else M₀.c ρ
  c_indep := by
    intro v m r r' k
    by_cases h1 : (Sum.inr v : Row D) = Sum.inl v₀
    · exact absurd h1 (by simp)
    by_cases h2 : (Sum.inr v : Row D) = Sum.inr v₀
    · simp only [h1, h2, ite_false, ite_true]
      exact L.indepC v₀ rfl m r r' k
    · simp only [h1, h2, ite_false]
      exact M₀.c_indep v m r r' k
  b := fun ρ => if ρ = Sum.inl v₀ then K.b else if ρ = Sum.inr v₀ then L.b else M₀.b ρ
  b_ne_top := by
    intro ρ
    by_cases h1 : ρ = Sum.inl v₀
    · simp only [h1, ite_true]; exact K.b_ne_top
    by_cases h2 : ρ = Sum.inr v₀
    · simp only [h1, h2, ite_false, ite_true]; exact L.b_ne_top
    · simp only [h1, h2, ite_false]; exact M₀.b_ne_top ρ
  fs_bound := by
    intro ρ
    by_cases h1 : ρ = Sum.inl v₀
    · subst h1; simp only [ite_true]; exact K.fs
    by_cases h2 : ρ = Sum.inr v₀
    · subst h2; simp only [h1, ite_false, ite_true]; exact L.fs
    · simp only [h1, h2, ite_false]; exact M₀.fs_bound ρ

theorem mergeCR_clock_inl (cr₀ : ClockedRows3 D) (v₀ : D.S.VIdx) (K : RowData D θ (Sum.inl v₀))
    (L : RowData D θ (Sum.inr v₀)) (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ) :
    (mergeCR cr₀ v₀ K L).clock τ tt (Sum.inl v₀) = K.clk τ tt := by
  funext i; simp [ClockedRows3.clock, mergeCR, RowData.clk]

theorem mergeCR_clock_inr (cr₀ : ClockedRows3 D) (v₀ : D.S.VIdx) (K : RowData D θ (Sum.inl v₀))
    (L : RowData D θ (Sum.inr v₀)) (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ) :
    (mergeCR cr₀ v₀ K L).clock τ tt (Sum.inr v₀) = L.clk τ tt := by
  funext i; simp [ClockedRows3.clock, mergeCR, RowData.clk]

theorem mergeCR_clock_other (cr₀ : ClockedRows3 D) (v₀ : D.S.VIdx) (K : RowData D θ (Sum.inl v₀))
    (L : RowData D θ (Sum.inr v₀)) (τ : D.S.TVar → ℝ) (tt : Fin 3 → ℝ) (ρ : Row D) (h1 : ρ ≠ Sum.inl v₀)
    (h2 : ρ ≠ Sum.inr v₀) : (mergeCR cr₀ v₀ K L).clock τ tt ρ = cr₀.clock τ tt ρ := by
  funext i; simp [ClockedRows3.clock, mergeCR, h1, h2]

/-- The a.e. expansion of the merged family from that of the two vine rows and of the other rows of the ambient family. -/
theorem merge_hser (cr₀ : ClockedRows3 D) (M₀ : ClockedModes3 D θ) (v₀ : D.S.VIdx) (K : RowData D θ (Sum.inl v₀))
    (L : RowData D θ (Sum.inr v₀)) (hI : 0 < D.S.I) (hK : K.Ae hI) (hL : L.Ae hI)
    (h0 : ∀ tt ∈ outBox D, ∀ᵐ τ ∂(volume.restrict (D.timeDom hI (tt 0) (tt 1) (tt 2))), ∀ ρ : Row D,
      ρ ≠ Sum.inl v₀ → ρ ≠ Sum.inr v₀ → ∀ r k : Mom d,
        HasSum (fun m => M₀.c ρ m r k * fsPhase m (cr₀.clock τ tt ρ)) (cr₀.W ρ (cr₀.clock τ tt ρ) r k)) :
    ∀ tt ∈ outBox D, ∀ᵐ τ ∂(volume.restrict (D.timeDom hI (tt 0) (tt 1) (tt 2))), ∀ (ρ : Row D) (r k : Mom d),
      HasSum (fun m => (mergeCM M₀ v₀ K L).c ρ m r k * fsPhase m ((mergeCR cr₀ v₀ K L).clock τ tt ρ))
        ((mergeCR cr₀ v₀ K L).W ρ ((mergeCR cr₀ v₀ K L).clock τ tt ρ) r k) := by
  intro tt htt
  filter_upwards [hK tt htt, hL tt htt, h0 tt htt] with τ h1 h2 h3 ρ r k
  by_cases e1 : ρ = Sum.inl v₀
  · subst e1
    rw [mergeCR_clock_inl]
    simpa [mergeCR, mergeCM] using h1 r k
  by_cases e2 : ρ = Sum.inr v₀
  · subst e2
    rw [mergeCR_clock_inr]
    simpa [mergeCR, mergeCM, e1] using h2 r k
  · rw [mergeCR_clock_other cr₀ v₀ K L τ tt ρ e1 e2]
    simpa [mergeCR, mergeCM, e1, e2] using h3 ρ e1 e2 r k

/-- The product of the mode sizes of the merged family. -/
theorem prod_mergeCM_b (M₀ : ClockedModes3 D θ) (v₀ : D.S.VIdx) (K : RowData D θ (Sum.inl v₀))
    (L : RowData D θ (Sum.inr v₀)) :
    ∏ ρ, (mergeCM M₀ v₀ K L).b ρ =
      K.b * L.b * ∏ ρ ∈ ((Finset.univ : Finset (Row D)).erase (Sum.inl v₀)).erase (Sum.inr v₀), M₀.b ρ := by
  have hne : (Sum.inr v₀ : Row D) ≠ Sum.inl v₀ := by simp
  have e1 : ∏ ρ, (mergeCM M₀ v₀ K L).b ρ =
      (mergeCM M₀ v₀ K L).b (Sum.inl v₀) * ∏ ρ ∈ (Finset.univ : Finset (Row D)).erase (Sum.inl v₀),
        (mergeCM M₀ v₀ K L).b ρ := (Finset.mul_prod_erase _ _ (Finset.mem_univ _)).symm
  have e2 : ∏ ρ ∈ (Finset.univ : Finset (Row D)).erase (Sum.inl v₀), (mergeCM M₀ v₀ K L).b ρ =
      (mergeCM M₀ v₀ K L).b (Sum.inr v₀) * ∏ ρ ∈ ((Finset.univ : Finset (Row D)).erase (Sum.inl v₀)).erase (Sum.inr v₀),
        (mergeCM M₀ v₀ K L).b ρ :=
    (Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩)).symm
  rw [e1, e2, ← mul_assoc]
  have e3 : ∏ ρ ∈ ((Finset.univ : Finset (Row D)).erase (Sum.inl v₀)).erase (Sum.inr v₀), (mergeCM M₀ v₀ K L).b ρ =
      ∏ ρ ∈ ((Finset.univ : Finset (Row D)).erase (Sum.inl v₀)).erase (Sum.inr v₀), M₀.b ρ := by
    refine Finset.prod_congr rfl fun ρ hρ => ?_
    have h2 := (Finset.mem_erase.1 hρ).1
    have h1 := (Finset.mem_erase.1 (Finset.mem_erase.1 hρ).2).1
    simp [mergeCM, h1, h2]
  rw [e3]
  simp [mergeCM]

end Merge

end WaveTurbulence.VineEstS5C.P2
