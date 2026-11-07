/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RemFar2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.PieceRowsR
public import WaveTurbulence.Foundations.Spine.PL2330Draft.Triangle

/-! # P4-W2 (session 8, R-SUPPLY): `RemC` on a window from the gate remainder at level `q`

`trC θ`: the real trace constant `≥ 1`.  `remC_window`: from the gate bound of `g` on `timeBox q q₂` (`XNormRestr (6η⁶) (30d) Λ₂ < CR`), `g` continuous in time, the
`RemC` on a window `w = q` (native) or `w ≥ q + 1` (the face trace at `t = q + 1`, `xnormRestr_face_trace`) with constant `trC · CR`; `remC_zero`: the zero remainder.
`pairBc`, `pairBcGt`: the open window pairs (continuity sets `Bc`). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS WaveTurbulence.Regref MeasureTheory Set
open scoped ENNReal

/-- The trace constant of the restriction norm `𝔛^{θ,·,·}` (real form). -/
noncomputable def trC (θ : ℝ) : ℝ := (Regref.traceConst (r := 2) θ Layered.chiUnit).toReal

theorem one_le_trC {θ : ℝ} (hθ : 0 ≤ θ) : 1 ≤ trC θ := by
  have h : 1 ≤ Regref.traceConst (r := 2) θ Layered.chiUnit :=
    Regref.one_le_traceConst hθ Layered.chiUnit_contDiff (t := fun _ => 0)
      (Layered.coordinateCutoff_chiUnit_eq_one fun i => by simp)
  unfold trC
  rw [← ENNReal.toReal_one]
  exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top (Layered.traceConst_chiUnit_ne_top θ)).2 h

theorem ofReal_trC (θ : ℝ) : ENNReal.ofReal (trC θ) = Regref.traceConst (r := 2) θ Layered.chiUnit :=
  ENNReal.ofReal_toReal (Layered.traceConst_chiUnit_ne_top θ)


variable {P : WTParams}

/-- **A remainder kernel on a window from the gate remainder at level `q`** (native window `w = q`, or a window above the gate level, `q + 1 ≤ w`, by the face
trace at `t = q + 1`).  On the continuity set `Bc` the kernel is `g` at `(min t (q+1), s)`. -/
theorem remC_window {Λ₂ : ℕ} (hd : 1 ≤ P.d) (hθ0 : 0 ≤ 6 * P.η ^ 6) {q q2 w : ℝ} {Bn Bw Bc : Set (Fin 2 → ℝ)}
    (hBwb : Bw ⊆ timeBox w q2) (hcell : Bw ⊆ cell ![w, q2]) (hint : Bw ⊆ closure (interior Bw))
    (hBc : Bc ⊆ Bw) (hBci : Bc ⊆ closure (interior Bc))
    (hface : ∀ s ∈ Icc q2 (q2 + 1), ![q + 1, s] ∈ closure (interior Bn))
    (g : (Fin 2 → ℝ) → Mom P.d → ℂ) (hg : ∀ k, Continuous fun ts => g ts k) {CR : ℝ} (hCR : 0 < CR)
    (hX : XNormRestr (6 * P.η ^ 6) (30 * P.d) Λ₂ Bn Set.univ g < ENNReal.ofReal CR)
    (hw : (w = q ∧ Bw = Bn) ∨ q + 1 ≤ w) :
    ∃ R : RemC P Λ₂ Bw ![w, q2] (trC (6 * P.η ^ 6) * CR), R.Bc = Bc ∧
      ∀ ts ∈ Bc, ∀ k, R.f ts k = g ![min (ts 0) (q + 1), ts 1] k := by
  have hT1 := one_le_trC hθ0
  have hCR' : 0 ≤ trC (6 * P.η ^ 6) * CR := by positivity
  have hΛ : 30 * P.d ≠ 0 := by omega
  rcases hw with ⟨rfl, rfl⟩ | hw
  · refine ⟨⟨g, Bc, hcell, hint, hBc, hBci, fun k => (hg k).continuousOn, hCR', ?_⟩, rfl, ?_⟩
    · refine lt_of_lt_of_le hX (ENNReal.ofReal_le_ofReal ?_)
      nlinarith
    · intro ts hts k
      have h2 := (hBwb (hBc hts)).1.2
      show g ts k = g ![min (ts 0) (w + 1), ts 1] k
      rw [min_eq_left h2]
      congr 1
      funext i; fin_cases i <;> rfl
  · refine ⟨⟨fun ts k => g ![q + 1, ts 1] k, Bc, hcell, hint, hBc, hBci, fun k => ?_, hCR', ?_⟩, rfl, ?_⟩
    · refine Continuous.continuousOn ?_
      refine (hg k).comp ?_
      refine continuous_pi fun i => ?_
      fin_cases i
      · exact continuous_const
      · exact continuous_apply 1
    · have h1 := xnormRestr_face_trace (d := P.d) hθ0 hΛ (Λ₂ := Λ₂) g hg q q2 w (Bn := Bn) (Bw := Bw)
        (fun t ht => hBwb ht) hface
      refine lt_of_le_of_lt h1 ?_
      rw [← ofReal_trC, ENNReal.ofReal_mul (by linarith)]
      exact (ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_pos.2 (by linarith)).ne' ENNReal.ofReal_ne_top).2 hX
    · intro ts hts k
      have h2 : (q : ℝ) + 1 ≤ ts 0 := le_trans hw (hBwb (hBc hts)).1.1
      show g ![q + 1, ts 1] k = g ![min (ts 0) (q + 1), ts 1] k
      rw [min_eq_right h2]


theorem xnormRestr_zero_fun {d : ℕ} (θ : ℝ) (Λ Λ₂ : ℕ) (B : Set (Fin 2 → ℝ)) :
    XNormRestr θ Λ Λ₂ B Set.univ (fun (_ : Fin 2 → ℝ) (_ : Mom d) => (0 : ℂ)) = 0 := by
  rw [PL2330.XNormRestr_eq_rN, PL2330.rN_eq_agreement]
  refine le_antisymm ?_ zero_le
  refine (iInf₂_le (fun _ _ => (0 : ℂ)) (fun _ _ _ _ => rfl)).trans (le_of_eq ?_)
  exact PL2330.mixedFourierNorm_zero θ Λ Λ₂

/-- The zero remainder on a window. -/
theorem remC_zero {Λ₂ : ℕ} {q2 w : ℝ} {Bw Bc : Set (Fin 2 → ℝ)} (hcell : Bw ⊆ cell ![w, q2]) (hint : Bw ⊆ closure (interior Bw))
    (hBc : Bc ⊆ Bw) (hBci : Bc ⊆ closure (interior Bc)) {CR : ℝ} (hCR : 0 < CR) :
    ∃ R : RemC P Λ₂ Bw ![w, q2] CR, R.Bc = Bc ∧ ∀ ts ∈ Bc, ∀ k, R.f ts k = 0 :=
  ⟨⟨fun _ _ => 0, Bc, hcell, hint, hBc, hBci, fun _ => continuousOn_const, hCR.le,
    by rw [xnormRestr_zero_fun]; exact ENNReal.ofReal_pos.2 hCR⟩, rfl, fun _ _ _ => rfl⟩

/-- The open window pair of a couple. -/
def pairBc (w q2 : ℝ) : Set (Fin 2 → ℝ) := {ts | ts 0 ∈ Ioo w (w + 1) ∧ ts 1 ∈ Ioo q2 (q2 + 1)}

/-- The open window pair of a tree (above the diagonal). -/
def pairBcGt (w q2 : ℝ) : Set (Fin 2 → ℝ) := {ts | (ts 0 ∈ Ioo w (w + 1) ∧ ts 1 ∈ Ioo q2 (q2 + 1)) ∧ ts 1 < ts 0}

theorem isOpen_pairBc (w q2 : ℝ) : IsOpen (pairBc w q2) :=
  (isOpen_Ioo.preimage (continuous_apply 0)).inter (isOpen_Ioo.preimage (continuous_apply 1))

theorem isOpen_pairBcGt (w q2 : ℝ) : IsOpen (pairBcGt w q2) :=
  ((isOpen_Ioo.preimage (continuous_apply 0)).inter (isOpen_Ioo.preimage (continuous_apply 1))).inter
    (isOpen_lt (f := fun ts : Fin 2 → ℝ => ts 1) (g := fun ts : Fin 2 → ℝ => ts 0) (continuous_apply 1) (continuous_apply 0))

theorem pairBc_subset (w q2 : ℝ) : pairBc w q2 ⊆ timeBox w q2 :=
  fun _ h => ⟨⟨h.1.1.le, h.1.2.le⟩, ⟨h.2.1.le, h.2.2.le⟩⟩

theorem pairBcGt_subset (w q2 : ℝ) : pairBcGt w q2 ⊆ timeBoxGt w q2 :=
  fun _ h => ⟨⟨⟨h.1.1.1.le, h.1.1.2.le⟩, ⟨h.1.2.1.le, h.1.2.2.le⟩⟩, h.2⟩

theorem pairBc_closure (w q2 : ℝ) : pairBc w q2 ⊆ closure (interior (pairBc w q2)) := by
  rw [(isOpen_pairBc w q2).interior_eq]; exact subset_closure

theorem pairBcGt_closure (w q2 : ℝ) : pairBcGt w q2 ⊆ closure (interior (pairBcGt w q2)) := by
  rw [(isOpen_pairBcGt w q2).interior_eq]; exact subset_closure

end WaveTurbulence.VineEstS5C.P4.W2
