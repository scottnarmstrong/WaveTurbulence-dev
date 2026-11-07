/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.TimeModes
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Merge

/-! # P2: row data of the vine rows (4d-A items (i), (iii)): separated rows and the joint three-clock row

* **`sepRow2_exists`**: the row `W(c, r, k) = J(c₀, c₁) · M(r, k)` (a two-clock time factor `J` with a restriction-norm bound on
  a box `B₂`, an arbitrary spatial factor `M(r,k)` with `S^{wN, rowOrder}` bound uniform in `r`) is a `RowData` with
  `b = C β sup_r ‖M(r)‖`.  Slots `(v₀, v₁, v₀)` (the third clock is not read: zero third mode).
* **`jointRow_exists`**: the row `W(c, r, k) = |c₀-c₁|^{-(1-3η)} (J(c₀,c₂) - J(c₁,c₂)) · M(r,k)` of clause (c) (three clocks
  `t₁, s₁, t₀`; `jointRow_modes`), `b = C β sup_r ‖M(r)‖`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P2
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.NormBridgeScratch MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

/-- **Separated two-clock rows.** -/
theorem sepRow2_exists {θ θ' : ℝ} (hθ : 0 ≤ θ) (hθθ : θ ≤ θ') :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum d) (hI : 0 < D.S.I) (ρ : Row D) (v : Fin 2 → D.S.TVar)
      (hv : Function.Injective v) (q : Fin 2 → ℝ) (B2 : Set (Fin 2 → ℝ)) (J : (Fin 2 → ℝ) → ℂ) (β : ℝ≥0∞)
      (M : Mom d → Mom d → ℂ), β ≠ ⊤ → B2 ⊆ cell q → B2 ⊆ closure (interior B2) →
      XNorm00Restr (V := Unit) θ' B2 Set.univ (fun ts _ => J ts) < β →
      (⨆ r : Mom d, SNorm D.wN (rowOrder D ρ) (M r)) ≠ ⊤ →
      (∀ w, ρ = Sum.inr w → ∀ r r' k : Mom d, M r k = M r' k) →
      (∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), (fun i => τ (v i)) ∈ B2) →
      ∃ R : RowData D θ ρ,
        (∀ c r k, R.W c r k = J ![c 0, c 1] * M r k) ∧
        (∀ i, R.slot i = Sum.inl (![v 0, v 1, v 0] i)) ∧
        R.b = C * β * ⨆ r : Mom d, SNorm D.wN (rowOrder D ρ) (M r) ∧ R.Ae hI := by
  obtain ⟨C, hC, hF⟩ := scalar2_modes3 hθ hθθ
  refine ⟨C, hC, fun D hI ρ v hv q B2 J β M hβ hc hi hJ hMfin hMind hclock => ?_⟩
  obtain ⟨ĥ, hae, hs⟩ := hF q B2 J β hc hi hJ
  have hbfin : C * β * ⨆ r : Mom d, SNorm D.wN (rowOrder D ρ) (M r) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hC hβ) hMfin
  have hfs : coefBound θ D.wN (rowOrder D ρ) (sepCoef ĥ M) ≤ C * β * ⨆ r : Mom d, SNorm D.wN (rowOrder D ρ) (M r) :=
    (coefBound_sep_le θ D.wN (rowOrder D ρ) ĥ M).trans (mul_le_mul_left hs _)
  refine ⟨{ W := fun c r k => J ![c 0, c 1] * M r k
            slot := fun i => Sum.inl (![v 0, v 1, v 0] i)
            c := sepCoef ĥ M
            b := C * β * ⨆ r : Mom d, SNorm D.wN (rowOrder D ρ) (M r)
            b_ne_top := hbfin
            fs := hfs
            indepW := fun w hw c r r' k => by rw [hMind w hw r r' k]
            indepC := fun w hw m r r' k => by unfold sepCoef; rw [hMind w hw r r' k] },
    fun _ _ _ => rfl, fun _ => rfl, rfl, ?_⟩
  intro tt htt
  refine ae_clock_box hI tt v hv (P := fun t => t ∈ B2 → ∀ s : Fin 3 → ℝ, ![s 0, s 1] = t →
    HasSum (fun m : Fin 3 → ℤ => ĥ m * fsPhase m s) (J t)) (by filter_upwards [hae] with t ht using ht) (hclock tt htt) ?_
  intro τ hP hB r k
  have e : ![slotVal D τ tt (Sum.inl (![v 0, v 1, v 0] 0)), slotVal D τ tt (Sum.inl (![v 0, v 1, v 0] 1))] =
      fun i => τ (v i) := by
    funext i; fin_cases i <;> rfl
  have hs3 := hP hB (fun i => slotVal D τ tt (Sum.inl (![v 0, v 1, v 0] i))) e
  rw [← e] at hs3
  exact hasSum_sepCoef hs3 M r k

/-- **The joint three-clock row of clause (c).** -/
theorem jointRow_exists {η θ : ℝ} (hη0 : 0 < η) (hη4 : η < 1 / 4) (hθ0 : 0 ≤ θ) (hθη : θ ≤ η) (Rb : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum d) (hI : 0 < D.S.I) (w₀ : D.S.VIdx) (v : Fin 3 → D.S.TVar)
      (hv : Function.Injective v) (q : Fin 3 → ℝ) (B2 : Set (Fin 2 → ℝ)) (B3 : Set (Fin 3 → ℝ))
      (J : (Fin 2 → ℝ) → ℂ) (β : ℝ≥0∞) (M : Mom d → Mom d → ℂ), β ≠ ⊤ → B3 ⊆ cell q →
      B3 ⊆ closure (interior B3) → (∀ τ ∈ B3, ‖τ‖ ≤ Rb) → (∀ τ ∈ B3, ![τ 0, τ 2] ∈ B2 ∧ ![τ 1, τ 2] ∈ B2) →
      XNorm00Restr (V := Unit) (1 - η) B2 Set.univ (fun ts _ => J ts) < β →
      (⨆ r : Mom d, SNorm D.wN (rowOrder D (Sum.inl w₀)) (M r)) ≠ ⊤ →
      (∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), (fun i => τ (v i)) ∈ B3) →
      ∃ R : RowData D θ (Sum.inl w₀),
        (∀ c r k, R.W c r k = ((((|c 0 - c 1| ^ (-(1 - 3 * η)) : ℝ) : ℂ) * (J ![c 0, c 2] - J ![c 1, c 2])) * M r k)) ∧
        (∀ i, R.slot i = Sum.inl (v i)) ∧
        R.b = C * β * ⨆ r : Mom d, SNorm D.wN (rowOrder D (Sum.inl w₀)) (M r) ∧ R.Ae hI := by
  obtain ⟨C, hC, hF⟩ := jointRow_modes (d := d) hη0 hη4 hθ0 hθη Rb
  refine ⟨C, hC, fun D hI w₀ v hv q B2 B3 J β M hβ hc hi hR hB hJ hMfin hclock => ?_⟩
  obtain ⟨c, hae, hcb⟩ := hF J B2 B3 q β M D.wN (rowOrder D (Sum.inl w₀)) hβ hc hi hR hB hJ
  have hbfin : C * β * ⨆ r : Mom d, SNorm D.wN (rowOrder D (Sum.inl w₀)) (M r) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hC hβ) hMfin
  refine ⟨{ W := fun c r k => ((((|c 0 - c 1| ^ (-(1 - 3 * η)) : ℝ) : ℂ) * (J ![c 0, c 2] - J ![c 1, c 2])) * M r k)
            slot := fun i => Sum.inl (v i)
            c := c
            b := C * β * ⨆ r : Mom d, SNorm D.wN (rowOrder D (Sum.inl w₀)) (M r)
            b_ne_top := hbfin
            fs := hcb
            indepW := fun w hw => absurd hw (by simp)
            indepC := fun w hw => absurd hw (by simp) },
    fun _ _ _ => rfl, fun _ => rfl, rfl, ?_⟩
  · intro tt htt
    refine ae_clock_box hI tt v hv (P := fun x : Fin 3 → ℝ => x ∈ B3 → ∀ r k : Mom d,
      HasSum (fun m : Fin 3 → ℤ => c m r k * fsPhase m x)
        ((((|x 0 - x 1| ^ (-(1 - 3 * η)) : ℝ) : ℂ) * (J ![x 0, x 2] - J ![x 1, x 2])) * M r k)) hae (hclock tt htt) ?_
    intro τ hP hB' r k
    exact hP hB' r k

/-- **Remainder rows** (clause (d)): an `r`-independent two-clock row `f(c₀,c₁,k)` with a restriction-norm bound
(`rowModes3_of_restr`; `f` continuous in time).  `D.wN = Λ₁`, `rowOrder D ρ = Λ₂`. -/
theorem remRow_exists {θ : ℝ} (hθ : 0 ≤ θ) (Λ₁ Λ₂ : ℕ) (hΛ : Λ₁ ≠ 0) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum d) (hI : 0 < D.S.I) (ρ : Row D), D.wN = Λ₁ → rowOrder D ρ = Λ₂ →
      ∀ (v : Fin 2 → D.S.TVar) (hv : Function.Injective v) (q : Fin 2 → ℝ) (B : Set (Fin 2 → ℝ))
      (f : (Fin 2 → ℝ) → Mom d → ℂ) (b : ℝ≥0∞),
      b ≠ ⊤ → B ⊆ cell q → B ⊆ closure (interior B) → (∀ k, Continuous fun t => f t k) →
      XNormRestr θ Λ₁ Λ₂ B Set.univ f < b →
      (∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), (fun i => τ (v i)) ∈ B) →
      ∃ R : RowData D θ ρ, (∀ c r k, R.W c r k = f ![c 0, c 1] k) ∧
        (∀ i, R.slot i = Sum.inl (![v 0, v 1, v 0] i)) ∧ R.b = C * b ∧ R.Ae hI := by
  obtain ⟨C, hC, hF⟩ := rowModes3_of_restr (d := d) hθ (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ
  refine ⟨C, hC, fun D hI ρ h1 h2 v hv q B f b hb hc hi hcont hX hclock => ?_⟩
  obtain ⟨c, hcs, hcb⟩ := hF q B f b hc hi hcont hX
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
  refine ae_clock_box hI tt v hv (P := fun _ => True) (Filter.Eventually.of_forall fun _ => trivial) (hclock tt htt) ?_
  intro τ _ hB r k
  have e : ![slotVal D τ tt (Sum.inl (![v 0, v 1, v 0] 0)), slotVal D τ tt (Sum.inl (![v 0, v 1, v 0] 1))] ∈ B := by
    have : ![slotVal D τ tt (Sum.inl (![v 0, v 1, v 0] 0)), slotVal D τ tt (Sum.inl (![v 0, v 1, v 0] 1))] =
      fun i => τ (v i) := by funext i; fin_cases i <;> rfl
    rw [this]; exact hB
  exact hcs (fun i => slotVal D τ tt (Sum.inl (![v 0, v 1, v 0] i))) e k

end WaveTurbulence.VineEstS5C.P2
