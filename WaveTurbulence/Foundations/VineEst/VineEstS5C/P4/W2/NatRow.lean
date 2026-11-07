/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.OfModes
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Mono
public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSMain
public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Embed

/-! # P4-W2 (step 3): the native rows as `RowData`

`natRowData`: a two-clock row function `f t k` (continuous in the clock pair `t`, `XNormRestr (6η⁶) (30 d) Λ₂ B2 univ f < β`, `B2` a unit box)
is the weight of a `RowData` of any slot triple: its modes are the Fourier modes of `f` (`fs_expansion`) embedded with third mode `0`
(`embedK`); the weight equals `f (c₀, c₁) k` wherever `(c₀, c₁) ∈ B2` (`RowData.ofModes_W`) and `Ae` holds at every clock (`RowData.ofModes_ae`).
The size is `≤ C β` with `C` depending on `d, η` only (`fs_expansion` at the derivative order `30 d - 1 = wN`, by `XNormRestr_mono_idx`). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- The two-clock vector-valued mode family embedded as a three-clock one (third mode `0`, no `r` dependence). -/
noncomputable def embedK (c : (Fin 2 → ℤ) → Mom d → ℂ) : (Fin 3 → ℤ) → Mom d → Mom d → ℂ :=
  fun m _ k => if m 2 = 0 then c ![m 0, m 1] k else 0

theorem embedK_eq_embed2 (c : (Fin 2 → ℤ) → Mom d → ℂ) (m : Fin 3 → ℤ) (r k : Mom d) :
    embedK c m r k = embed2 (fun n => c n k) m := rfl

theorem hasSum_embedK (c : (Fin 2 → ℤ) → Mom d → ℂ) (t : Fin 3 → ℝ) (r k : Mom d) {S : ℂ}
    (hS : HasSum (fun n : Fin 2 → ℤ => c n k * fsPhase n ![t 0, t 1]) S) :
    HasSum (fun m : Fin 3 → ℤ => embedK c m r k * fsPhase m t) S :=
  hasSum_embed2 (fun n => c n k) t hS

theorem embedK_embedMode (c : (Fin 2 → ℤ) → Mom d → ℂ) (n : Fin 2 → ℤ) (r : Mom d) :
    embedK c (embedMode n) r = c n := by
  funext k
  rw [embedK_eq_embed2, embed2_embedMode]

theorem embedK_eq_zero (c : (Fin 2 → ℤ) → Mom d → ℂ) (m : Fin 3 → ℤ) (hm : m ∉ Set.range embedMode) (r : Mom d) :
    embedK c m r = fun _ => 0 := by
  funext k
  rw [embedK_eq_embed2, embed2_eq_zero _ m hm]

theorem coefBound_embedK (θ : ℝ) (A B : ℕ) (c : (Fin 2 → ℤ) → Mom d → ℂ) :
    coefBound θ A B (embedK c) = ∑' n : Fin 2 → ℤ, maxBracketPow θ (half n) * SNorm A B (c n) := by
  unfold coefBound
  have hs : ∀ (m : Fin 3 → ℤ), (⨆ r : Mom d, SNorm A B (embedK c m r)) = SNorm A B (embedK c m 0) := fun m => by
    have : ∀ r : Mom d, embedK c m r = embedK c m 0 := fun r => rfl
    simp only [this]
    exact iSup_const
  simp only [hs]
  rw [← embedMode_injective.tsum_eq (f := fun m : Fin 3 → ℤ => maxBracketPow θ (half m) * SNorm A B (embedK c m 0))]
  · refine tsum_congr fun n => ?_
    rw [maxBracketPow_embedMode, embedK_embedMode]
  · intro m hm
    by_contra hnr
    apply hm
    simp [embedK_eq_zero c m hnr 0, SNorm_zero']

/-- **A native two-clock row as a `RowData`** (any slot triple). -/
theorem natRowData (d : ℕ) (η : ℝ) (hd : 1 ≤ d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (D : SumintPar.SumintDatum d) (hI : 0 < D.S.I) (hwN : D.wN + 1 = 30 * d) (hwDec : D.wDec = 30 * d)
      (ρ : Row D) (slot : Fin 3 → WaveTurbulence.VineEstS3Par.Eng.Slot D) (q : Fin 2 → ℝ) (B2 : Set (Fin 2 → ℝ))
      (f : (Fin 2 → ℝ) → Mom d → ℂ) (β : ℝ≥0∞), β ≠ ⊤ → B2 ⊆ cell q → B2 ⊆ closure (interior B2) →
      (∀ k, Continuous fun t => f t k) →
      XNormRestr (6 * η ^ 6) (30 * d) (rowOrder D ρ) B2 Set.univ f < β →
      ∃ R : RowData D (6 * η ^ 6) ρ,
        (∀ cl : Fin 3 → ℝ, ![cl 0, cl 1] ∈ B2 → ∀ r k, R.W cl r k = f ![cl 0, cl 1] k) ∧
        (∀ i, R.slot i = slot i) ∧ R.b ≤ C * β ∧ R.Ae hI ∧ (∀ cl r k, R.W cl r k = ∑' m, R.c m r k * fsPhase m cl) := by
  have hθ : (0 : ℝ) ≤ 6 * η ^ 6 := by positivity
  have hΛ : 30 * d - 1 ≠ 0 := by omega
  obtain ⟨C₁, hC₁, hF₁⟩ := fs_expansion (r := 2) (d := d) hθ (Λ₁ := 30 * d - 1) (Λ₂ := 30 * d) hΛ
  obtain ⟨C₂, hC₂, hF₂⟩ := fs_expansion (r := 2) (d := d) hθ (Λ₁ := 30 * d - 1) (Λ₂ := 0) hΛ
  refine ⟨max C₁ C₂, max_lt hC₁.lt_top hC₂.lt_top |>.ne, fun D hI hwN hwDec ρ slot q B2 f β hβ hc hi hcont hres => ?_⟩
  have hwN' : D.wN = 30 * d - 1 := by omega
  have hres' : XNormRestr (6 * η ^ 6) (30 * d - 1) (rowOrder D ρ) B2 Set.univ f < β :=
    lt_of_le_of_lt (XNormRestr_mono_idx (by omega) le_rfl B2 Set.univ f) hres
  have hmain : ∃ c : (Fin 2 → ℤ) → Mom d → ℂ,
      (∀ t ∈ B2, ∀ k, HasSum (fun m : Fin 2 → ℤ => c m k * fsPhase m t) (f t k)) ∧
      ∑' m : Fin 2 → ℤ, maxBracketPow (6 * η ^ 6) (half m) * SNorm (30 * d - 1) (rowOrder D ρ) (c m) ≤
        max C₁ C₂ * β := by
    rcases ρ with v | v
    · have e : rowOrder D (Sum.inl v) = 30 * d := by simp [rowOrder, hwDec]
      rw [e] at hres' ⊢
      obtain ⟨c, h1, h2⟩ := hF₁ q B2 Set.univ f β hc hi (fun k _ => hcont k) hres'
      exact ⟨c, fun t ht k => h1 t ht k (Set.mem_univ k), h2.trans (mul_le_mul_left (le_max_left _ _) _)⟩
    · have e : rowOrder D (Sum.inr v) = 0 := by simp [rowOrder]
      rw [e] at hres' ⊢
      obtain ⟨c, h1, h2⟩ := hF₂ q B2 Set.univ f β hc hi (fun k _ => hcont k) hres'
      exact ⟨c, fun t ht k => h1 t ht k (Set.mem_univ k), h2.trans (mul_le_mul_left (le_max_right _ _) _)⟩
  obtain ⟨c, hsum, hb⟩ := hmain
  have hfs : coefBound (6 * η ^ 6) D.wN (rowOrder D ρ) (embedK c) ≤ max C₁ C₂ * β := by
    rw [coefBound_embedK, hwN']
    exact hb
  have hbt : max C₁ C₂ * β ≠ ⊤ := ENNReal.mul_ne_top (max_lt hC₁.lt_top hC₂.lt_top |>.ne) hβ
  refine ⟨RowData.ofModes (θ := 6 * η ^ 6) ρ slot (embedK c) (max C₁ C₂ * β) hbt hfs (fun v _ m r r' k => rfl),
    fun cl hcl r k => ?_, fun i => rfl, le_rfl, RowData.ofModes_ae hθ hI ρ slot (embedK c) _ hbt hfs _, fun cl r k => rfl⟩
  exact RowData.ofModes_W (hasSum_embedK c cl r k (hsum _ hcl k))

end WaveTurbulence.VineEstS5C.P4.W2
