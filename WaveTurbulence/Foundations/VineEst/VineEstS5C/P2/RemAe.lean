/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.FSAe
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Rows

/-! # P2: remainder rows, a.e. version (step 3; the continuity ruling)

`rowModes3_of_restr_ae`, `remRow_ae_exists`: the row `f(c₀,c₁,k)` of a kernel that agrees (a.e. in time on the box, all `k`) with a
function `f'` continuous in time (this is the case of `K* - app`; `K*` is continuous in time (`continuous_KQstar_time`), the
approximant is a finite sum of separated terms) has the engine datum `RowData` with the a.e. mode expansion. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.NormBridgeScratch MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

theorem rowModes3_of_restr_ae {θ : ℝ} (hθ : 0 ≤ θ) {Λ₁ Λ₂ : ℕ} (hΛ : Λ₁ ≠ 0) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (q : Fin 2 → ℝ) (B : Set (Fin 2 → ℝ)) (f f' : (Fin 2 → ℝ) → Mom d → ℂ) (b : ℝ≥0∞),
      B ⊆ cell q → B ⊆ closure (interior B) → (∀ k, Continuous fun t => f' t k) →
      (∀ᵐ t, t ∈ B → ∀ k, f t k = f' t k) → XNormRestr θ Λ₁ Λ₂ B Set.univ f < b →
      ∃ c : (Fin 3 → ℤ) → Mom d → ℂ,
        (∀ t3 : Fin 3 → ℝ, ![t3 0, t3 1] ∈ B → ∀ k, HasSum (fun m : Fin 3 → ℤ => c m k * fsPhase m t3)
          (f' ![t3 0, t3 1] k)) ∧
        ∑' m : Fin 3 → ℤ, maxBracketPow θ (half m) * SNorm Λ₁ Λ₂ (c m) ≤ C * b := by
  obtain ⟨C, hC, hf⟩ := fs_expansion_ae (r := 2) (d := d) hθ hΛ
  refine ⟨C, hC, fun q B f f' b hBc hBi hfc hae hb => ?_⟩
  obtain ⟨c2, h1, h2⟩ := hf q B f f' b hBc hBi hfc hae hb
  refine ⟨fun m k => embed2 (fun n => c2 n k) m, fun t3 ht3 k => ?_, ?_⟩
  · exact hasSum_embed2 (fun n => c2 n k) t3 (h1 _ ht3 k)
  · refine le_trans (le_of_eq ?_) h2
    rw [← embedMode_injective.tsum_eq (f := fun m : Fin 3 → ℤ => maxBracketPow θ (half m) *
      SNorm Λ₁ Λ₂ (fun k => embed2 (fun n => c2 n k) m))]
    · refine tsum_congr fun n => ?_
      rw [maxBracketPow_embedMode]
      congr 2
      funext k
      rw [embed2_embedMode]
    · intro m hm
      by_contra hnr
      apply hm
      have : (fun k => embed2 (fun n => c2 n k) m) = fun _ => 0 := funext fun k => embed2_eq_zero _ m hnr
      simp [this, SNorm_zero_fun]

/-- **Remainder rows** (clause (d)), a.e. version: the row `f(c₀,c₁,k)` with `f = f'` a.e. in time on the box, `f'` continuous in
time, `XNormRestr θ Λ₁ Λ₂ B univ f < b`. -/
theorem remRow_ae_exists {θ : ℝ} (hθ : 0 ≤ θ) (Λ₁ Λ₂ : ℕ) (hΛ : Λ₁ ≠ 0) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum d) (hI : 0 < D.S.I) (ρ : Row D), D.wN = Λ₁ → rowOrder D ρ = Λ₂ →
      ∀ (v : Fin 2 → D.S.TVar) (hv : Function.Injective v) (q : Fin 2 → ℝ) (B : Set (Fin 2 → ℝ))
      (f f' : (Fin 2 → ℝ) → Mom d → ℂ) (b : ℝ≥0∞),
      b ≠ ⊤ → B ⊆ cell q → B ⊆ closure (interior B) → (∀ k, Continuous fun t => f' t k) →
      (∀ᵐ t, t ∈ B → ∀ k, f t k = f' t k) →
      XNormRestr θ Λ₁ Λ₂ B Set.univ f < b →
      (∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), (fun i => τ (v i)) ∈ B) →
      ∃ R : RowData D θ ρ, (∀ c r k, R.W c r k = f ![c 0, c 1] k) ∧
        (∀ i, R.slot i = Sum.inl (![v 0, v 1, v 0] i)) ∧ R.b = C * b ∧ R.Ae hI := by
  obtain ⟨C, hC, hF⟩ := rowModes3_of_restr_ae (d := d) hθ (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ
  refine ⟨C, hC, fun D hI ρ h1 h2 v hv q B f f' b hb hc hi hcont hae hX hclock => ?_⟩
  obtain ⟨c, hcs, hcb⟩ := hF q B f f' b hc hi hcont hae hX
  have hfs : coefBound θ D.wN (rowOrder D ρ) (fun m _ k => c m k) ≤ C * b := by
    unfold coefBound
    rw [h1, h2]
    refine le_trans (le_of_eq (tsum_congr fun m => ?_)) hcb
    congr 1
    exact iSup_const
  refine ⟨{ W := fun cc _ k => f ![cc 0, cc 1] k
            slot := fun i => Sum.inl (![v 0, v 1, v 0] i)
            c := fun m _ k => c m k
            b := C * b
            b_ne_top := ENNReal.mul_ne_top hC hb
            fs := hfs
            indepW := fun _ _ _ _ _ _ => rfl
            indepC := fun _ _ _ _ _ _ => rfl },
    fun _ _ _ => rfl, fun _ => rfl, rfl, ?_⟩
  intro tt htt
  refine ae_clock_box hI tt v hv (P := fun t => t ∈ B → ∀ k, f t k = f' t k) hae (hclock tt htt) ?_
  intro τ hP hB r k
  have hx : ![slotVal D τ tt (Sum.inl (![v 0, v 1, v 0] 0)), slotVal D τ tt (Sum.inl (![v 0, v 1, v 0] 1))] =
      fun i => τ (v i) := by funext i; fin_cases i <;> rfl
  have e : ![slotVal D τ tt (Sum.inl (![v 0, v 1, v 0] 0)), slotVal D τ tt (Sum.inl (![v 0, v 1, v 0] 1))] ∈ B := by
    rw [hx]; exact hB
  have := hcs (fun i => slotVal D τ tt (Sum.inl (![v 0, v 1, v 0] i))) e k
  have hk : f ![slotVal D τ tt (Sum.inl (![v 0, v 1, v 0] 0)), slotVal D τ tt (Sum.inl (![v 0, v 1, v 0] 1))] k =
      f' ![slotVal D τ tt (Sum.inl (![v 0, v 1, v 0] 0)), slotVal D τ tt (Sum.inl (![v 0, v 1, v 0] 1))] k := by
    rw [hx]; exact hP hB k
  show HasSum _ (f ![slotVal D τ tt (Sum.inl (![v 0, v 1, v 0] 0)), slotVal D τ tt (Sum.inl (![v 0, v 1, v 0] 1))] k)
  rw [hk]
  exact this

end WaveTurbulence.VineEstS5C.P2
