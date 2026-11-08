/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.OuterFix
public import WaveTurbulence.Foundations.Flower.SelRes.Triv
public import WaveTurbulence.Foundations.Stage1.Represents.RepVN10

/-! # B3s-HELPER4 (δ) S1 (0): the `lb`-independent basics of B3s's pinned engine

Copied by source from the world file `MkSlots/EngDefs.lean` (B3s; sha256 `48932148…d23e`, see `COPIED-SHA256SUMS`),
lines 54–98 (`atomWF`, `atomW_eq_atomWF`, `norm_atomWF_le`, `pieceAtomW`, `pieceAtomW_eq_atomWF`,
`pieceAtomW_eq_atomW`, `extendFix_eq_extendFixI_fun`) and 161–193 (`RepIntCMK`, `repBoundMK`,
`RepIntCMK.toRepresentsIntMK`), into namespace `WaveTurbulence.Flower.MkSlotsS`. These do not read the time domain of
`splicedTimeIntegralMK`; copying them keeps the selected engine independent of the ruling-R187 (`lb`) repair of the other
lemmas of `EngDefs.lean`. The definitions are verbatim, hence definitionally equal to B3s's. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots

namespace WaveTurbulence.Flower.MkSlotsS

variable {w d : ℕ}

-- [copied] MkSlots/EngDefs.lean L54-98
def atomWF {G : Garden w} (filt : GBranch G.tree → Option (ℝ × SchwartzMap ℝ ℂ))
    (ind : (GNode G.tree → Mom d) → ℝ) (k : GNode G.tree → Mom d) : ℂ :=
  (∏ a : GBranch G.tree, (filt a).elim 1 fun q => q.2 (omegaNode G k a / q.1)) * (ind k : ℂ)

theorem atomW_eq_atomWF {G : Garden w} (D : SplicedKernelDataMK G d) (k : GNode G.tree → Mom d) :
    D.atomW k = atomWF D.filt D.ind k := rfl

theorem norm_atomWF_le {G : Garden w} (filt : GBranch G.tree → Option (ℝ × SchwartzMap ℝ ℂ))
    (ind : (GNode G.tree → Mom d) → ℝ) (hfilt : ∀ a q, filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1)
    (hind : ∀ k, 0 ≤ ind k ∧ ind k ≤ 1) (k : GNode G.tree → Mom d) : ‖atomWF filt ind k‖ ≤ 1 := by
  unfold atomWF
  rw [norm_mul, norm_prod]
  have h1 : ∏ a, ‖(filt a).elim 1 fun q => q.2 (omegaNode G k a / q.1)‖ ≤ 1 := by
    refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun a _ => ?_
    rcases h : filt a with _ | q
    · simp
    · exact hfilt a q h _
  have h2 : ‖((ind k : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (hind k).1]; exact (hind k).2
  calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The atom weight of a marked piece: filters and indicator of `π` (`SplicedKernelDataMK.atomW` of `π.dataMK`, which
does not depend on the other data fields). -/
def pieceAtomW {d R : ℕ} (π : Stage1PieceMK d R) (k : GNode π.Gsb.tree → Mom d) : ℂ :=
  (∏ a, (π.filt a).elim 1 fun q => q.2 (omegaNode π.Gsb k a / q.1)) * (π.ind k : ℂ)

theorem pieceAtomW_eq_atomWF {d R : ℕ} (π : Stage1PieceMK d R) (k : GNode π.Gsb.tree → Mom d) :
    pieceAtomW π k = atomWF π.filt π.ind k := rfl

theorem pieceAtomW_eq_atomW {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (tt : Fin (2 * R) → ℝ)
    (center : GardenDart π.Gsb → Mom P.d) (edge : GardenDart π.Gsb → Mom P.d → ℂ)
    (hinge : (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ) (freq : GBranch π.Gsb.tree → ℝ)
    (k : GNode π.Gsb.tree → Mom P.d) :
    pieceAtomW π k = (π.dataMK tt center edge hinge freq).atomW k := rfl

/-! ## The pinned measure on the spliced time domain -/

theorem extendFix_eq_extendFixI_fun (G : Garden w) (fix : GBranch G.tree → Option ℝ) :
    G.extendFix fix = extendFixI fix := by
  funext τ b
  rcases h : fix b with _ | v
  · rw [WaveTurbulence.Flower.FlFace.extendFix_of_none fix τ b h, extendFixI_none fix τ h]
  · rw [WaveTurbulence.Flower.FlFace.extendFix_of_some fix τ b h, extendFixI_some fix τ h]

-- [end copied]

-- [copied] MkSlots/EngDefs.lean L161-193
/-! ## The count-measure form of `RepresentsIntMK` (pinned `RepIntC`, RepRep1) -/

/-- The count-measure form of `RepresentsIntMK`, with explicit mass bound `B`. -/
def RepIntCMK {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (val : ℂ) (B : ℝ) : Prop :=
  ∃ (Ξ : Type) (_ : Countable Ξ) (w : Ξ → ℂ) (ctr : Ξ → GardenDart π.Gsb → Mom P.d)
    (edge : Ξ → GardenDart π.Gsb → Mom P.d → ℂ)
    (hinge : Ξ → (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ) (freq : Ξ → GBranch π.Gsb.tree → ℝ),
    Summable (fun ξ => ‖w ξ * splicedKernelMK π.Gsb (π.dataMK tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots‖) ∧
    val = ∑' ξ, w ξ * splicedKernelMK π.Gsb (π.dataMK tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots ∧
    Summable (fun ξ => ‖w ξ‖) ∧ ∑' ξ, ‖w ξ‖ ≤ B ∧
    ∀ ξ, SplicedAmplitudeBounds π.Gsb (Stage1Piece.data π.toStage1PieceD tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))

/-- The bound of `RepresentsIntMK`. -/
def repBoundMK (P : WTParams) {R : ℕ} (π : Stage1PieceMK P.d R) (n : ℕ) (cP s : ℝ) : ℝ :=
  (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
    P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
      P.L ^ (cP * P.d * (π.nProt : ℝ)) * s

theorem RepIntCMK.toRepresentsIntMK {P : WTParams} {R : ℕ} {π : Stage1PieceMK P.d R} {tt : Fin (2 * R) → ℝ}
    {base : Mom P.d} {roots : Fin (2 * R) → (Fin P.d → ℤ)} {val : ℂ} {B : ℝ}
    (h : RepIntCMK π tt base roots val B) (n : ℕ) (cP s : ℝ) (hB : B ≤ repBoundMK P π n cP s) :
    π.RepresentsIntMK n cP tt base roots s val := by
  obtain ⟨Ξ, hc, w, ctr, edge, hinge, freq, h1, h2, h3, h4, h5⟩ := h
  let _ : MeasurableSpace Ξ := ⊤
  have : MeasurableSingletonClass Ξ := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  obtain ⟨hint, hint2⟩ := integral_count_eq_tsum _ h1
  obtain ⟨hint', hint2'⟩ := integral_count_real_eq_tsum _ h3.norm
  refine ⟨Ξ, inferInstance, Measure.count, w, ctr, edge, hinge, freq, hint, ?_, hint', ?_, h5⟩
  · rw [hint2]; exact h2
  · rw [hint2']; exact h4.trans hB
-- [end copied]

end WaveTurbulence.Flower.MkSlotsS
