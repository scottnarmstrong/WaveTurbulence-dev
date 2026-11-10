/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPin.Domain
import Mathlib.Tactic

/-! # C4a PIN-FOURIER: reductions between the box sums

- `boxSumGen_mono`: shrinking the exceptional set `E` can only increase the box sum (a box on `Eᶜ` extends by `⌊β⌋`
  on `E \ E₀`).
- `splicedFourierBMK_eq_face`: the pins-only transform is the face transform with no substitution, so
  `LadderFourierAtMK` follows from `LadderFourierAtMKFace` (`ladderFourierAtMK_of_face`).
- `ladderFourierAt_of_MK`: with no pins and `E = ∅` the MK box sum is main's `splicedFourierBoxSum`, so
  `LadderFourierAtMK P → LadderFourierAt P` (the bridge, SCOPE §4.3). -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Flower.FinalMKPin
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Ladder WaveTurbulence.Flower.FinalMKDefs
open MeasureTheory Set Finset
open scoped Classical ENNReal

variable {w : ℕ} {G : Garden w}

/-- The box sum of `LadderFourierAtMK(Face)` for an arbitrary integrand `F`. -/
noncomputable def boxSumGen (G : Garden w) (E : Finset (GBranch G.tree)) (β : GBranch G.tree → ℝ)
    (A : Set (GBranch G.tree → ℝ)) (F : (GBranch G.tree → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' σ : sourceFrequencyBoxesE G E {α | α ∈ A ∧ ∀ v ∈ E, α v = β v},
    ⨆ (α : GBranch G.tree → ℝ) (_ : α ∈ A) (_ : ∀ v ∈ E, α v = β v)
      (_ : ∀ v : {b : GBranch G.tree // b ∉ E}, |α v.1 - σ.1 v| ≤ 1), F α

theorem boxSumMKFace_eq_gen (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) (fix : GBranch G.tree → Option ℝ)
    (face : GBranch G.tree → Option (GBranch G.tree)) (E : Finset (GBranch G.tree)) (β : GBranch G.tree → ℝ)
    (A : Set (GBranch G.tree → ℝ)) :
    splicedFourierBoxSumMKFace G layer rootTime fix face E β A =
      boxSumGen G E β A (fun α => ‖splicedFourierBMKFace G layer rootTime fix face α‖ₑ) := rfl

/-- **Shrinking the exceptional set.** -/
theorem boxSumGen_mono {E E₀ : Finset (GBranch G.tree)} (hE : E₀ ⊆ E) (β : GBranch G.tree → ℝ)
    (A : Set (GBranch G.tree → ℝ)) (F : (GBranch G.tree → ℝ) → ℝ≥0∞) :
    boxSumGen G E β A F ≤ boxSumGen G E₀ β A F := by
  unfold boxSumGen
  set S := sourceFrequencyBoxesE G E {α | α ∈ A ∧ ∀ v ∈ E, α v = β v}
  set S₀ := sourceFrequencyBoxesE G E₀ {α | α ∈ A ∧ ∀ v ∈ E₀, α v = β v}
  let ext : ({b : GBranch G.tree // b ∉ E} → ℤ) → ({b : GBranch G.tree // b ∉ E₀} → ℤ) :=
    fun σ v => if h : v.1 ∈ E then ⌊β v.1⌋ else σ ⟨v.1, h⟩
  have hmem : ∀ σ : S, ext σ.1 ∈ S₀ := by
    rintro ⟨σ, α, ⟨hαA, hαE⟩, hασ⟩
    refine ⟨α, ⟨hαA, fun v hv => hαE v (hE hv)⟩, fun v => ?_⟩
    by_cases h : v.1 ∈ E
    · simp only [ext, dif_pos h, hαE v.1 h]
    · simp only [ext, dif_neg h]; exact hασ ⟨v.1, h⟩
  let φ : S → S₀ := fun σ => ⟨ext σ.1, hmem σ⟩
  have hinj : Function.Injective φ := by
    intro σ σ' h
    apply Subtype.ext
    funext v
    have := congrFun (congrArg Subtype.val h) ⟨v.1, fun hv => v.2 (hE hv)⟩
    simpa [φ, ext, v.2] using this
  refine le_trans ?_ (ENNReal.tsum_comp_le_tsum_of_injective hinj _)
  refine ENNReal.tsum_le_tsum fun σ => ?_
  refine iSup_le fun α => iSup_le fun hα => iSup_le fun hαE => iSup_le fun hασ => ?_
  refine le_iSup_of_le α (le_iSup_of_le hα (le_iSup_of_le (fun v hv => hαE v (hE hv))
    (le_iSup_of_le (fun v => ?_) le_rfl)))
  by_cases h : v.1 ∈ E
  · simp only [φ, ext, dif_pos h, hαE v.1 h]
    rw [abs_le]; constructor <;> linarith [Int.floor_le (β v.1), Int.lt_floor_add_one (β v.1)]
  · simp only [φ, ext, dif_neg h]; exact hασ ⟨v.1, h⟩

/-! ### Pins only = no substitution -/

theorem integral_pi_subtype_congr {ι : Type*} [Fintype ι] (p q : ι → Prop) [DecidablePred p] [DecidablePred q]
    (hpq : ∀ i, p i ↔ q i) (H : ({i // q i} → ℝ) → ℂ) :
    ∫ σ : {i // p i} → ℝ, H (fun i => σ ⟨i.1, (hpq i.1).mpr i.2⟩) = ∫ τ : {i // q i} → ℝ, H τ := by
  let e : {i // p i} ≃ {i // q i} := Equiv.subtypeEquivRight hpq
  have hmp := measurePreserving_piCongrLeft (fun _ : {i // q i} => (volume : Measure ℝ)) e
  have := hmp.integral_comp' (f := MeasurableEquiv.piCongrLeft (fun _ : {i // q i} => ℝ) e) H
  convert this using 2 with σ
  funext σ
  congr 1

theorem splicedFourierBMK_eq_face (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) (α : GBranch G.tree → ℝ) :
    splicedFourierBMK G layer rootTime fix α = splicedFourierBMKFace G layer rootTime fix (fun _ => none) α := by
  unfold splicedFourierBMK splicedFourierBMKFace
  rw [← integral_pi_subtype_congr (fun b => fix b = none) (fun b => fix b = none ∧ (none : Option (GBranch G.tree)) = none)
    (fun b => by simp)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  have hdom : splicedTimeDomainFace G layer rootTime fix (fun _ => none) = splicedTimeDomainFix G layer rootTime fix := by
    ext t
    simp [splicedTimeDomainFace, splicedTimeDomainFix]
  have hext : extendFixFace G fix (fun _ => none) (fun i => σ ⟨i.1, i.2.1⟩) = G.extendFix fix σ := by
    funext b
    rw [extendFixFace_eq]
    unfold Garden.extendFix
    split
    · next r hr => simp [hr]
    · next hr => simp [hr, ttv, repV]
  simp only
  rw [hdom, hext]

theorem boxSumMK_eq_face (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) (fix : GBranch G.tree → Option ℝ)
    (E : Finset (GBranch G.tree)) (β : GBranch G.tree → ℝ) (A : Set (GBranch G.tree → ℝ)) :
    splicedFourierBoxSumMK G layer rootTime fix E β A =
      splicedFourierBoxSumMKFace G layer rootTime fix (fun _ => none) E β A := by
  unfold splicedFourierBoxSumMK splicedFourierBoxSumMKFace
  simp only [splicedFourierBMK_eq_face]

/-- `LadderFourierAtMK` is the `face ≡ none` case of `LadderFourierAtMKFace`. -/
theorem ladderFourierAtMK_of_face (P : WTParams) (h : LadderFourierAtMKFace P) : LadderFourierAtMK P := by
  intro p hp R hR hRmax G hpl hir hbal hn hnmax D fix E scales hlay hamp hfixE hfixL base roots β
  rw [boxSumMK_eq_face]
  exact h p hp R hR hRmax G hpl hir hbal hn hnmax D fix (fun _ => none) E scales hlay hamp hfixE hfixL
    (fun v u h => by simp at h) (fun v v' h => by simp at h) base roots β

/-! ### The bridge to main's `LadderFourierAt` -/

end WaveTurbulence.Flower.FinalMKPin
