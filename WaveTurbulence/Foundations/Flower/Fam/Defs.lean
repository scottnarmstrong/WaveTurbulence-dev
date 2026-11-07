/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Typed.Defs
public import WaveTurbulence.Foundations.Flower.Cases.Defs
public import WaveTurbulence.Foundations.Spine.SchwartzUniformNorm
public import WaveTurbulence.Foundations.Spine.RemainderInputs
public import WaveTurbulence.Foundations.Spine.SpatialInputBounds
/-! # FL-FAM definitions: the two ANALYTIC TARGETS `FlowerCoreFiltAt`, `FlowerCoreGainAt`, and the
concrete constants `C`, `U`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Fam
open Set WaveTurbulence.Flower.Typed WaveTurbulence.Flower.Cases

/-- **ANALYTIC TARGET F (filtered, unmarked flower estimate).**  Profiles `h` with `S^{40d,40d}` bound `b`,
frontier cutoffs `Rf` (radius `≥ L/2`), stem filters `σ`; no root decay is asked.  Deviation from the plan
text (ruled by wt-orch): `P.L / 2 ≤ r` and `r ^ 10 ≤ ‖latticePoint P.L n‖`. -/
def FlowerCoreFiltAt (Bc : ℕ → ℝ) (Pm : ℕ) (P : WTParams) : Prop :=
  1 / 2 < P.γ → ∀ p : ℕ, p < P.D →
    ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
    ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
      (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d))
      (h : ℕ → Fin (2 * Pm) → Fin (2 * Pm) → Mom P.d → ℝ) (b : ℝ), 1 ≤ b →
      (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
    ∀ (Rf : Fin (2 * Pm) → Option ℝ) (σ : Fin (2 * Pm) → Option ℕ),
      (∀ j r, Rf j = some r → P.L / 2 ≤ r) →
      ((∃ i, σ i ≠ none) → ∀ j, ∃ r, Rf j = some r ∧
        (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L n‖) →
    ‖FC23.flowerWeighted P (fun _ _ => 1) p N kind pat dagger
        (fun LG k => frontierW LG p Rf k * stemFilter LG P.L σ k * leafProd LG h k) ζ t s n n'‖ ≤
      P.L ^ (Bc P.d * Pm) * P.δ ^ (6 * P.ν * N) * b ^ N

/-- **ANALYTIC TARGET G (selected-face gain, plain patterns, positive shell).**  Same edits as target F. -/
def FlowerCoreGainAt (Bc : ℕ → ℝ) (Pm : ℕ) (P : WTParams) : Prop :=
  1 / 2 < P.γ → ∀ p : ℕ, p < P.D →
    ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
    ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d))
      (h : ℕ → Fin (2 * Pm) → Fin (2 * Pm) → Mom P.d → ℝ) (b : ℝ), 1 ≤ b →
      (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
    ∀ (Rf : Fin (2 * Pm) → ℝ) (j₂ : ℕ), 0 < j₂ → (∀ j, P.L / 2 ≤ Rf j) →
      (∀ j, (∀ j' x, ‖x‖ ≥ Rf j → h p j j' x = 0 ∧ h p j' j x = 0) ∧
        Rf j ^ 10 ≤ ‖latticePoint P.L n‖) →
    ‖FC23.flowerWeighted P (fun _ _ => 1) p N kind (fun _ => .plain) dagger
        (fun LG k => frontierW LG p (fun j => some (Rf j)) k * LG.cutWeight2P P.L j₂ k * leafProd LG h k)
        ζ t s n n'‖ ≤
      P.L ^ (Bc P.d * Pm) * P.δ ^ (6 * P.ν * N) * b ^ N * ((2 : ℝ) ^ j₂ * P.L) ^ (-(Pm / 9 : ℝ))

/-- The uniform `S^{A,B}` bound of the WKE solution on `[0, τ*]` (a fixed choice; `1` if none). -/
def unifBound (P : WTParams) (A B : ℕ) : ℝ :=
  if h : ∃ C : ℝ, 1 ≤ C ∧ ∀ τ ∈ Icc (0 : ℝ) P.τstar, SNormR A B (P.φ τ) ≤ ENNReal.ofReal C
  then h.choose else 1

theorem unifBound_spec (P : WTParams) (hsol : ContinuousOn P.φ (Icc 0 P.τstar)) (A B : ℕ) :
    1 ≤ unifBound P A B ∧ ∀ τ ∈ Icc (0 : ℝ) P.τstar, SNormR A B (P.φ τ) ≤ ENNReal.ofReal (unifBound P A B) := by
  have h := LGSpine.exists_uniform_SNormR hsol A B
  unfold unifBound
  rw [dif_pos h]
  exact h.choose_spec

/-- The constant `C d := 1`. -/
def Cfam : ℕ → ℝ := fun _ => 1

/-- The high-weight constant: bound at `(Λ₀, Λ₀)` plus one (for the remainder). -/
def Ufam (P : WTParams) (_p : ℕ) : ℝ := unifBound P (P.Lambda 0) (P.Lambda 0) + 1

/-- The low constant: bound at `(40d, 40d)` plus one, independent of `δ`. -/
def Ulow (P : WTParams) : ℝ := unifBound P (40 * P.d) (40 * P.d) + 1

theorem Cfam_pos : ∀ d, 0 < Cfam d := fun _ => one_pos

theorem Ufam_pos : ∀ P p, 0 < Ufam P p := by
  intro P p
  unfold Ufam
  have : 1 ≤ unifBound P (P.Lambda 0) (P.Lambda 0) := by
    unfold unifBound
    split_ifs with h
    · exact h.choose_spec.1
    · exact le_rfl
  linarith

theorem Ufam_L (P : WTParams) (L : ℝ) (p : ℕ) : Ufam {P with L := L} p = Ufam P p := rfl

theorem Ufam_one (P : WTParams) (p : ℕ) : 1 ≤ Ufam P p := by
  have := Ufam_pos P p
  unfold Ufam at *
  have : 1 ≤ unifBound P (P.Lambda 0) (P.Lambda 0) := by
    unfold unifBound
    split_ifs with h
    · exact h.choose_spec.1
    · exact le_rfl
  linarith

theorem one_le_Ulow (P : WTParams) : 1 ≤ Ulow P := by
  unfold Ulow
  have : 1 ≤ unifBound P (40 * P.d) (40 * P.d) := by
    unfold unifBound
    split_ifs with h
    · exact h.choose_spec.1
    · exact le_rfl
  linarith

end WaveTurbulence.Flower.Fam
