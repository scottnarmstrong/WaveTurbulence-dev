/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcBnd
public import WaveTurbulence.Foundations.VineEst.VineEstS3.DomainLayerOrder

/-! # W2-KIND2 (interface): the cross-window fields `XCross` that W2 adds to `Src`, the cross box, and the size lemma

`XCross P S RQ RT q2 q4 qh src`: for every good index `b` and every couple term `i`, tree term `j`, ONE time factor `xJq b i`, `xJt b j` that
agrees with the certified time factors of the LOW window (`src.cq false`, `src.ct false`) on their continuity sets and with those of the HIGH
window (`src.cq true`, `src.ct true`) on theirs (the spatial factors and coefficients coincide: `xq_M`, `src.cq_c`), is continuous on `Bcq`/`Bct`,
and is bounded in `𝔛^{1-2η}(Bq)`, `𝔛^{1-2η}(Bt)` with `Bq`, `Bt` containing the clock pairs of BOTH open windows.  The bound is uniform:
`CJxq b ≤ Kx · src.CJq b`.  W2 produces these fields from the gate expansion by `K2.xq_of_gate` (far: separated union; adjacent: clamp gluing).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2.K2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS4c
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2
  MeasureTheory
open scoped ENNReal

/-- The cross-window clock pairs: `t` in `(q4, q4+1) ∪ (qh, qh+1)`, `s` in `(q2, q2+1)` (and `s < t` for trees). -/
def XWin (B Bc : Set (Fin 2 → ℝ)) (q4 qh q2 : ℝ) (gt : Bool) : Prop :=
  ∀ t ∈ Set.Ioo q4 (q4 + 1) ∪ Set.Ioo qh (qh + 1), ∀ s ∈ Set.Ioo q2 (q2 + 1), (gt = true → s < t) → ![t, s] ∈ B ∧ ![t, s] ∈ Bc

/-- **The cross-window fields of `Src`** (`q4 + 1 ≤ qh`), with the `𝔛^{1-2η}` bounds. -/
structure XCross (P : WTParams) {β : Type*} {S : SepTerms β P.d} {RQ RT : β → ℝ → ℝ → Mom P.d → ℂ} {q2 q4 qh : ℝ}
    (src : Src P S RQ RT q2 q4 qh) where
  Bq : Set (Fin 2 → ℝ)
  Bcq : Set (Fin 2 → ℝ)
  Bt : Set (Fin 2 → ℝ)
  Bct : Set (Fin 2 → ℝ)
  xJq : ∀ b, Fin (S.mQ b) → (Fin 2 → ℝ) → ℂ
  xJt : ∀ b, Fin (S.mT b) → (Fin 2 → ℝ) → ℂ
  CJxq : β → ℝ
  CJxt : β → ℝ
  Kx : ℝ
  hKx : 1 ≤ Kx
  CJxq_nonneg : ∀ b, src.good b → 0 ≤ CJxq b
  CJxt_nonneg : ∀ b, src.good b → 0 ≤ CJxt b
  CJxq_le : ∀ b, src.good b → CJxq b ≤ Kx * src.CJq b
  CJxt_le : ∀ b, src.good b → CJxt b ≤ Kx * src.CJt b
  xq_win : ∀ b, src.good b → XWin Bq Bcq q4 qh q2 false
  xt_win : ∀ b, src.good b → XWin Bt Bct q4 qh q2 true
  xq_cont : ∀ b, src.good b → ∀ i, ContinuousOn (xJq b i) Bcq
  xt_cont : ∀ b, src.good b → ∀ j, ContinuousOn (xJt b j) Bct
  xq_norm : ∀ b, src.good b → ∀ i,
    XNorm00Restr (V := Unit) (1 - 2 * P.η) Bq Set.univ (fun ts _ => xJq b i ts) < ENNReal.ofReal (CJxq b)
  xt_norm : ∀ b, src.good b → ∀ j,
    XNorm00Restr (V := Unit) (1 - 2 * P.η) Bt Set.univ (fun ts _ => xJt b j ts) < ENNReal.ofReal (CJxt b)
  xq_M : ∀ b, src.good b → ∀ i, (src.cq true b i).M = (src.cq false b i).M
  xt_M : ∀ b, src.good b → ∀ j, (src.ct true b j).M = (src.ct false b j).M
  xq_lo : ∀ b, src.good b → ∀ i, ∀ ts ∈ (src.cq false b i).Bc, xJq b i ts = (src.cq false b i).J ts
  xq_hi : ∀ b, src.good b → ∀ i, ∀ ts ∈ (src.cq true b i).Bc, xJq b i ts = (src.cq true b i).J ts
  xt_lo : ∀ b, src.good b → ∀ j, ∀ ts ∈ (src.ct false b j).Bc, xJt b j ts = (src.ct false b j).J ts
  xt_hi : ∀ b, src.good b → ∀ j, ∀ ts ∈ (src.ct true b j).Bc, xJt b j ts = (src.ct true b j).J ts

/-- The open cross box of three clocks. -/
def crossBoxG (qa qb q2 : ℝ) : Set (Fin 3 → ℝ) :=
  {τ | τ 0 ∈ Set.Ioo qa (qa + 1) ∧ τ 1 ∈ Set.Ioo qb (qb + 1) ∧ τ 2 ∈ Set.Ioo q2 (q2 + 1)}

theorem crossBoxG_isOpen (qa qb q2 : ℝ) : IsOpen (crossBoxG qa qb q2) :=
  (isOpen_Ioo.preimage (continuous_apply 0)).inter ((isOpen_Ioo.preimage (continuous_apply 1)).inter
    (isOpen_Ioo.preimage (continuous_apply 2)))

theorem crossBoxG_sub_cell (qa qb q2 : ℝ) : crossBoxG qa qb q2 ⊆ cell ![qa, qb, q2] := by
  intro τ hτ i
  fin_cases i
  · exact ⟨hτ.1.1.le, hτ.1.2.le⟩
  · exact ⟨hτ.2.1.1.le, hτ.2.1.2.le⟩
  · exact ⟨hτ.2.2.1.le, hτ.2.2.2.le⟩

theorem crossBoxG_ne {qa qb q2 : ℝ} (hgap : qa + 1 ≤ qb ∨ qb + 1 ≤ qa) : ∀ τ ∈ crossBoxG qa qb q2, τ 0 ≠ τ 1 := by
  intro τ hτ h
  have h1 := hτ.1
  have h2 := hτ.2.1
  rw [h] at h1
  rcases hgap with g | g <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem crossBoxG_norm {qa qb q2 Rb : ℝ} (ha : 0 ≤ qa) (hb : 0 ≤ qb) (h2 : 0 ≤ q2) (hRa : qa + 1 ≤ Rb) (hRb : qb + 1 ≤ Rb)
    (hR2 : q2 + 1 ≤ Rb) : ∀ τ ∈ crossBoxG qa qb q2, ‖τ‖ ≤ Rb := by
  intro τ hτ
  have hR0 : (0 : ℝ) ≤ Rb := by linarith
  refine (pi_norm_le_iff_of_nonneg hR0).2 fun i => ?_
  fin_cases i
  · show ‖τ 0‖ ≤ Rb
    rw [Real.norm_eq_abs, abs_of_pos (by linarith [hτ.1.1])]; linarith [hτ.1.2]
  · show ‖τ 1‖ ≤ Rb
    rw [Real.norm_eq_abs, abs_of_pos (by linarith [hτ.2.1.1])]; linarith [hτ.2.1.2]
  · show ‖τ 2‖ ≤ Rb
    rw [Real.norm_eq_abs, abs_of_pos (by linarith [hτ.2.2.1])]; linarith [hτ.2.2.2]

/-- The open cross box with `t₀` below both other clocks. -/
def crossBoxO (qa qb q2 : ℝ) : Set (Fin 3 → ℝ) := {τ | τ ∈ crossBoxG qa qb q2 ∧ τ 2 < τ 0 ∧ τ 2 < τ 1}

theorem crossBoxO_isOpen (qa qb q2 : ℝ) : IsOpen (crossBoxO qa qb q2) :=
  (crossBoxG_isOpen qa qb q2).inter ((isOpen_lt (continuous_apply 2) (continuous_apply 0)).inter
    (isOpen_lt (continuous_apply 2) (continuous_apply 1)))

theorem crossBoxO_cl (qa qb q2 : ℝ) : crossBoxO qa qb q2 ⊆ closure (interior (crossBoxO qa qb q2)) := by
  rw [(crossBoxO_isOpen qa qb q2).interior_eq]; exact subset_closure

/-- Absorbing the glue constant `Kx` into the uniform constant `K0`. -/
theorem bnd_x {d : ℕ} (hd : 1 ≤ d) (K0 : ℝ≥0∞) (Kx Z SZ : ℝ) (hKx : 1 ≤ Kx) (hZ : Z ≤ Kx * SZ) (hs : 0 ≤ SZ) :
    K0 * K0 * ENNReal.ofReal (Ksp d) * ENNReal.ofReal Z ≤ Kall d (K0 * ENNReal.ofReal Kx) * ENNReal.ofReal SZ := by
  unfold Kall
  have hK1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal Kx := by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hKx
  have hS1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Ksp d) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (one_le_Ksp hd)
  have h1 : 1 ≤ ENNReal.ofReal Kx * ENNReal.ofReal (Ksp d) := by
    calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
      _ ≤ _ := mul_le_mul' hK1 hS1
  calc K0 * K0 * ENNReal.ofReal (Ksp d) * ENNReal.ofReal Z
      ≤ K0 * K0 * ENNReal.ofReal (Ksp d) * ENNReal.ofReal (Kx * SZ) := mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hZ)
    _ = (K0 * K0 * ENNReal.ofReal Kx * ENNReal.ofReal (Ksp d) * ENNReal.ofReal SZ) * 1 := by
        rw [ENNReal.ofReal_mul (le_trans zero_le_one hKx)]; ring
    _ ≤ (K0 * K0 * ENNReal.ofReal Kx * ENNReal.ofReal (Ksp d) * ENNReal.ofReal SZ) *
          (ENNReal.ofReal Kx * ENNReal.ofReal (Ksp d)) := mul_le_mul' le_rfl h1
    _ = (K0 * ENNReal.ofReal Kx) * (K0 * ENNReal.ofReal Kx) * ENNReal.ofReal (Ksp d) * ENNReal.ofReal (Ksp d) *
          ENNReal.ofReal SZ := by ring

end WaveTurbulence.VineEstS5C.P4.W2.K2
