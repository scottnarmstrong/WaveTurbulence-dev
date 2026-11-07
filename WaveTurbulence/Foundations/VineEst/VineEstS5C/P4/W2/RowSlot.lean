/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.RemAe
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.Rows
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.OfModes

/-! # P4-W2 (c): a native row with arbitrary slots (`RowData` of a kernel continuous in time)

`remRowS`: the row `f(c₀,c₁,k)` of a kernel that is CONTINUOUS in time, with the clock slots `s : Fin 2 → Slot D` arbitrary (exterior times allowed, unlike
`remRowW` whose clocks are internal atoms): `f = f'` everywhere, so no a.e. step in the clocks is needed; `Ae` holds for every `τ` of the time domain.  This is the
form of the native rows `K_Q^*`, `K_T^*` of the region (`natCR3`, slots `natSlot`). -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.VineEstS5C.P4.W2
variable {d : ℕ}

/-- **A native row with arbitrary slots** (the clocks may be exterior times): `W = f(c₀,c₁,k)` for `f` continuous in time. -/
theorem remRowS {θ : ℝ} (hθ : 0 ≤ θ) (Λ₁ Λ₂ : ℕ) (hΛ : Λ₁ ≠ 0) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum d) (hI : 0 < D.S.I) (ρ : Row D), D.wN = Λ₁ → rowOrder D ρ = Λ₂ →
      ∀ (s : Fin 2 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (q : Fin 2 → ℝ) (B : Set (Fin 2 → ℝ)) (f : (Fin 2 → ℝ) → Mom d → ℂ) (b : ℝ≥0∞),
      b ≠ ⊤ → B ⊆ cell q → B ⊆ closure (interior B) → (∀ k, Continuous fun t => f t k) →
      XNormRestr θ Λ₁ Λ₂ B Set.univ f < b →
      ∃ R : RowData D θ ρ, (∀ cl r k, ![cl 0, cl 1] ∈ B → R.W cl r k = f ![cl 0, cl 1] k) ∧
        (∀ i, R.slot i = ![s 0, s 1, s 0] i) ∧ R.b = C * b ∧ R.Ae hI := by
  obtain ⟨C, hC, hF⟩ := rowModes3_of_restr_ae (d := d) hθ (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ
  refine ⟨C, hC, fun D hI ρ h1 h2 s q B f b hb hc hi hcont hX => ?_⟩
  obtain ⟨c, hcs, hcb⟩ := hF q B f f b hc hi hcont (Filter.Eventually.of_forall fun _ _ _ => rfl) hX
  have hfs : coefBound θ D.wN (rowOrder D ρ) (fun m _ k => c m k) ≤ C * b := by
    unfold coefBound
    rw [h1, h2]
    refine le_trans (le_of_eq (tsum_congr fun m => ?_)) hcb
    congr 1
    exact iSup_const
  refine ⟨RowData.ofModes (θ := θ) ρ ![s 0, s 1, s 0] (fun m _ k => c m k) (C * b) (ENNReal.mul_ne_top hC hb) hfs
    (fun _ _ _ _ _ _ => rfl), fun cl r k hcl => RowData.ofModes_W (hcs cl hcl k), fun _ => rfl, rfl,
    RowData.ofModes_ae hθ hI ρ _ _ _ _ _ _⟩

end WaveTurbulence.VineEstS5C.P4.W2
