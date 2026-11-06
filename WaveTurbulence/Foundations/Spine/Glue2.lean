/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Glue1
import Mathlib.Tactic
/-! Classes of the spectrum by presentation signature. -/
@[expose] public section
open WaveTurbulence.Induct
open Finset
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDisjoint
variable {w d : ℕ} (G : Garden w)

theorem IsLadderGap_transport_gen {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}
    (M : Molecule V D) {m m' : ℕ} (hmm : m = m') {u v : Fin (m + 1) → V} {u' v' : Fin (m' + 1) → V}
    (h : ∀ i ≤ m, rowN u i = rowN u' i ∧ rowN v i = rowN v' i) (L : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) (hm : 1 ≤ m) (hm' : 1 ≤ m') (r : Mom d) :
    M.IsLadderGap L w κ u v hm r ↔ M.IsLadderGap L w κ u' v' hm' r := by
  subst hmm
  exact IsLadderGap_transport M h L w κ hm r

/-- The admissible gap sizes in `sourceLadderGapScales`. -/
def gapOK (P : ℝ) {d : ℕ} (r : Mom d) : Prop :=
  (P = 0 → r = 0) ∧ (0 < P → P < 1 → P / 2 ≤ ‖r‖ ∧ ‖r‖ ≤ 2 * P) ∧ (P = 1 → 1 ≤ ‖r‖)

/-- Frequencies realized by a decoration whose ladder presentations are the family `π`. -/
def clsPF (D : SplicedKernelData G d) (scales : Finset (GBranch G.tree) → ℝ) (L γ η δ : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (π : PF G) : Set (GBranch G.tree → ℝ) :=
  {α | ∃ z : GenDecoration G d roots 0,
    splicedEpsilon G D.hinges z.1 ≠ 0 ∧ splicedGapIndicator G D L γ η base z.1 ≠ 0 ∧
    (∀ x ∈ G.molecule.bonds, ‖base + latticePoint L (bondIndex G z.1 x) - D.center x‖ ≤ 1) ∧
    sourceLadderGapScales G scales L base (bondIndex G z.1) ∧
    (∀ S : LQ G, ∃ hm : 1 ≤ π.m S, ∃ r, G.molecule.IsLadderGap L base (bondIndex G z.1) (π.u S) (π.v S) hm r ∧
      gapOK (scales S.1) r) ∧
    α = splicedFrequency G D L γ δ base z.1}

theorem spectrum_subset_iUnion (D : SplicedKernelData G d) (scales : Finset (GBranch G.tree) → ℝ)
    (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) :
    splicedFrequencySpectrum G D scales L γ η δ base roots ⊆
      ⋃ π : PF G, clsPF G D scales L γ η δ base roots π := by
  rintro α ⟨z, h1, h2, h3, h4, h5⟩
  have hS : ∀ S : LQ G, ∃ (m : ℕ) (u v : Fin (m + 1) → GBranch G.tree) (hm : 1 ≤ m),
      G.molecule.IsLadder u v ∧ Molecule.ladderAtoms u v = S.1 ∧
      ∃ r, G.molecule.IsLadderGap L base (bondIndex G z.1) u v hm r ∧ gapOK (scales S.1) r := by
    intro S
    obtain ⟨_, m, u, v, hm, hL, hat, r, hr, hr0, hr1, hr2⟩ := h4 S.1 S.2
    exact ⟨m, u, v, hm, hL, hat, r, hr, hr0, hr1, hr2⟩
  choose m u v hm hL hat r hr hgap using hS
  refine Set.mem_iUnion.mpr ⟨⟨m, u, v, hL, hat⟩, z, h1, h2, h3, h4, fun S => ⟨hm S, r S, hr S, hgap S⟩, h5⟩

theorem clsPF_transport (D : SplicedKernelData G d) (scales : Finset (GBranch G.tree) → ℝ)
    (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (π π0 : PF G) (h : π.sig = π0.sig) :
    clsPF G D scales L γ η δ base roots π ⊆ clsPF G D scales L γ η δ base roots π0 := by
  rintro α ⟨z, h1, h2, h3, h4, h5, h6⟩
  refine ⟨z, h1, h2, h3, h4, fun S => ?_, h6⟩
  obtain ⟨hm, r, hr, hg⟩ := h5 S
  have hmm := π.m_eq G π0 S
  refine ⟨by rw [← hmm]; exact hm, r, ?_, hg⟩
  exact (IsLadderGap_transport_gen G.molecule hmm (fun i hi => PF.rows_eq G π π0 h S hi) L base _ hm
    (by rw [← hmm]; exact hm) r).mp hr

end WaveTurbulence.Ladder
