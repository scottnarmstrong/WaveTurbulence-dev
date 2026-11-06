/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Glue6
import Mathlib.Tactic
/-! Atom-level localization and the sets `S_v`. -/
@[expose] public section
open Finset MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDisjoint
open scoped Classical
variable {w d : ℕ} {G : Garden w}

theorem clsPF_subset_spectrum (D : SplicedKernelData G d) (scales : Finset (GBranch G.tree) → ℝ)
    (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (π0 : PF G) :
    clsPF G D scales L γ η δ base roots π0 ⊆ splicedFrequencySpectrum G D scales L γ η δ base roots := by
  rintro α ⟨z, h1, h2, h3, h4, _, h6⟩
  exact ⟨z, h1, h2, h3, h4, h6⟩

theorem CD.ua_def {D : SplicedKernelData G d} {L γ δ : ℝ} {base : Mom d} {roots : Fin w → (Fin d → ℤ)}
    {hp : G.IsPlain} {π0 : PF G} {εS : LQ G → ℝ} (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop)
    (S : LQ G) (i : Fin (cd.Kn isSmall S)) :
    cd.ua isSmall ⟨S, i⟩ = rowN (π0.u S) (cd.enum isSmall S i) := by
  simp [CD.ua, atomAt]

theorem CD.va_def {D : SplicedKernelData G d} {L γ δ : ℝ} {base : Mom d} {roots : Fin w → (Fin d → ℤ)}
    {hp : G.IsPlain} {π0 : PF G} {εS : LQ G → ℝ} (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop)
    (S : LQ G) (i : Fin (cd.Kn isSmall S)) :
    cd.va isSmall ⟨S, i⟩ = rowN (π0.v S) (cd.enum isSmall S i) := by
  simp [CD.va, atomAt]

/-- The localization radius. -/
noncomputable def rhoS (d : ℕ) (L γ δ P : ℝ) : ℝ :=
  (1 + d * (2 : ℝ) ^ (d - 1)) * |8 * δ * L ^ (2 * γ) * P| + 2 + 2 * d * (2 : ℝ) ^ (d - 1)

theorem loc_atom (hp : G.IsPlain) {L : ℝ} (hL : 0 < L) (D : SplicedKernelData G d)
    (hamp : SplicedAmplitudeBounds G D) (scales : Finset (GBranch G.tree) → ℝ) (γ η δ : ℝ) (hδ : 0 ≤ δ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (π0 : PF G)
    (cd : CD G D L γ δ base roots hp π0 (fun S => 8 * δ * L ^ (2 * γ) * scales S.1))
    (isSmall : LQ G → Prop) (hsm : ∀ S, isSmall S → scales S.1 < 1)
    (θ : Jr (cd.Kn isSmall) → Bool) (s : Jr (cd.Kn isSmall))
    (α α' : GBranch G.tree → ℝ) (hα' : α' ∈ clsPF G D scales L γ η δ base roots π0)
    (hclose : ∀ b, |α b - α' b| ≤ 1) :
    |α (xθ (cd.ua isSmall) (cd.va isSmall) θ s) -
      cd.hXf isSmall θ (xθ (cd.ua isSmall) (cd.va isSmall) θ s) α| ≤ rhoS d L γ δ (scales s.1.1) := by
  obtain ⟨S, i⟩ := s
  have hj := cd.JS_sub isSmall S (cd.enum_mem isSmall S i)
  have hI : cd.enum isSmall S i ∈ Finset.Icc 1 (π0.m S - 1) := by
    rw [Finset.mem_Icc]; omega
  have hS := loc_S hp hL D hamp scales γ η δ hδ base roots π0 cd α α' hα' hclose S (hsm S hj.2.2)
    (cd.enum isSmall S i) hI
  have hinj := cd.elim_injective isSmall
  have hex : ∃ s', xθ (cd.ua isSmall) (cd.va isSmall) θ s' = xθ (cd.ua isSmall) (cd.va isSmall) θ ⟨S, i⟩ :=
    ⟨⟨S, i⟩, rfl⟩
  have hch : hex.choose = ⟨S, i⟩ :=
    xθ_injective _ _ hinj θ hex.choose_spec
  unfold CD.hXf
  rw [dite_eq_left hex, hch]
  have hsum : α (xθ (cd.ua isSmall) (cd.va isSmall) θ ⟨S, i⟩) +
      α (yθ (cd.ua isSmall) (cd.va isSmall) θ ⟨S, i⟩) =
      α (rowN (π0.u S) (cd.enum isSmall S i)) + α (rowN (π0.v S) (cd.enum isSmall S i)) := by
    have e1 := cd.ua_def isSmall S i
    have e2 := cd.va_def isSmall S i
    unfold xθ yθ
    rw [e1, e2]
    cases θ ⟨S, i⟩
    · simp only [Bool.false_eq_true, ite_false]; ring
    · simp only [ite_true]
  have hat : ∀ l, α (atomAt π0 S true (cd.r' S l)) + α (atomAt π0 S false (cd.r' S l)) =
      α (rowN (π0.u S) (cd.r' S l)) + α (rowN (π0.v S) (cd.r' S l)) := by
    intro l; simp [atomAt]
  simp only [hat]
  have : α (xθ (cd.ua isSmall) (cd.va isSmall) θ ⟨S, i⟩) -
      ((∑ l, cd.cc S (cd.enum isSmall S i) l * (α (rowN (π0.u S) (cd.r' S l)) + α (rowN (π0.v S) (cd.r' S l))) +
        cd.dd S (cd.enum isSmall S i)) - α (yθ (cd.ua isSmall) (cd.va isSmall) θ ⟨S, i⟩)) =
      (α (rowN (π0.u S) (cd.enum isSmall S i)) + α (rowN (π0.v S) (cd.enum isSmall S i))) -
        ∑ l, cd.cc S (cd.enum isSmall S i) l * (α (rowN (π0.u S) (cd.r' S l)) + α (rowN (π0.v S) (cd.r' S l))) -
        cd.dd S (cd.enum isSmall S i) := by
    linarith
  rw [this]
  exact hS

end WaveTurbulence.Ladder
