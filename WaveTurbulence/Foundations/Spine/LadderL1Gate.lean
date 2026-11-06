/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LadderL1Fixed
/-! # The time-L1 ladder gate (S3c COARSE-SPLICED)

`LadderL1At` is the time-L1 form of the ladder decay `LadderDecayAt` (TARGET redladder2,
L1978-L1992): for a ladder `u v`, the integral over the unit time box of the modulus of the finite
local lattice sum, times the coupling power of the ladder, has the same bound as the local kernel.
It is proved by the same parameter choices as `ladderDecayGate` (S3b). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.WeylSums WaveTurbulence.Sumint MeasureTheory Set Finset

abbrev LadderL1At (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ D : SplicedKernelData G P.d, SplicedAmplitudeBounds G D → (∀ v, D.layer v ≤ p) →
  ∀ (m : ℕ) (u v : Fin (m + 1) → GBranch G.tree), 1 ≤ m → G.molecule.IsLadder u v →
    Disjoint (Molecule.ladderAtoms u v) D.hinges →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ (boundary : GardenDart G → (Fin P.d → ℤ))
    (T0 : Finset ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary)),
    (∀ z, z ∉ T0 → ladderWeight D (Molecule.ladderAtoms u v) P.L P.γ P.η base z.1.1 = 0) →
    ‖(coupling P.d P.L P.γ P.δ : ℂ)‖ ^ ((Molecule.ladderAtoms u v).card - 1) *
      ∫ t in timeBox G D.layer (Molecule.ladderAtoms u v),
        ‖∑ z ∈ T0, ladderWeight D (Molecule.ladderAtoms u v) P.L P.γ P.η base z.1.1 *
          ladderPhase D (Molecule.ladderAtoms u v) P.L P.γ P.δ base z.1.1 t‖ ≤
      P.C₁ * (P.C₁ * P.δ) ^ m *
        P.L ^ (-(P.gamma1 - Real.sqrt P.η) * sourceLadderIncoherency G D.layer u v + 20 * P.d)

open Set in
/-- **The time-L1 ladder gate.** -/
theorem ladderL1Gate : WTPrefix LadderL1At := by
  intro d hd γ hγ
  obtain ⟨hγ0, hγ1⟩ := hγ
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1
  have hg1pos : 0 < g1 := by
    simp only [hg1]
    refine lt_min (by linarith) (lt_min one_pos ?_)
    nlinarith
  set η₀ : ℝ := min (min γ (1 - γ) / (10 * d)) ((g1 / 2) ^ 2) with hη₀
  have hη₀pos : 0 < η₀ := by
    refine lt_min ?_ (by positivity)
    apply div_pos (lt_min hγ0 (by linarith)) (by positivity)
  refine ⟨η₀, hη₀pos, ?_⟩
  intro η hη φin hφin τ hτ φ hφ
  obtain ⟨hη0, hηle⟩ := hη
  have hη1 : 10 * (d : ℝ) * η ≤ γ := by
    have h1 : η ≤ min γ (1 - γ) / (10 * d) := hηle.trans (min_le_left _ _)
    have h2 : 10 * (d : ℝ) * η ≤ min γ (1 - γ) := by
      rw [le_div_iff₀ (by positivity)] at h1; linarith
    exact h2.trans (min_le_left _ _)
  have hη2 : 10 * (d : ℝ) * η ≤ 1 - γ := by
    have h1 : η ≤ min γ (1 - γ) / (10 * d) := hηle.trans (min_le_left _ _)
    have h2 : 10 * (d : ℝ) * η ≤ min γ (1 - γ) := by
      rw [le_div_iff₀ (by positivity)] at h1; linarith
    exact h2.trans (min_le_right _ _)
  have hη1' : η ≤ 1 := by nlinarith
  have hsq : Real.sqrt η ≤ g1 / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    exact hηle.trans (min_le_right _ _)
  have hsqpos : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη0
  have hηsq : η ≤ Real.sqrt η := by
    have := Real.sqrt_le_sqrt hη1'
    nlinarith [Real.sq_sqrt hη0.le, Real.sqrt_nonneg η]
  set x : ℝ := g1 - Real.sqrt η with hx
  have hx0 : 0 ≤ x := by linarith
  have hx1 : x < 2 * γ := by
    have : g1 ≤ 2 * γ := min_le_left _ _
    linarith
  have hx2 : x ≤ 1 := by
    have : g1 ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hx3 : -2 * ((d : ℝ) - 1) * (1 - γ) + η ≤ -x := by
    have : g1 ≤ 2 * ((d : ℝ) - 1) * (1 - γ) := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  obtain ⟨C0, hC0, hrt⟩ := rung_total hd ⟨hγ0, hγ1⟩ hη0 hη1 hη2 hτ hx1 hx2 hx3
  set M : ℝ := 7 ^ d * cellFourierFactor d with hM
  set C1 : ℝ := 1 + 9 * M ^ 4 * C0 + 3 ^ (16 * d) * M ^ 2 with hC1
  have hMn : 0 ≤ M := by have := cellFourierFactor_nonneg d; positivity
  have hC1ge : 1 ≤ C1 := by
    have : 0 ≤ 9 * M ^ 4 * C0 := by positivity
    have : 0 ≤ 3 ^ (16 * d) * M ^ 2 := by positivity
    linarith
  refine ⟨C1, hC1ge, 1, one_pos, ?_⟩
  intro ν hν
  refine ⟨1, one_pos, ?_⟩
  intro δ hδ D hD hτD
  obtain ⟨L1, hL1, hL1'⟩ := hrt δ hδ.1 hδ.2
  refine ⟨1, le_rfl, max 2 L1, le_max_left _ _, ?_⟩
  intro L hL
  have hLL1 : L1 ≤ L := (le_max_right _ _).trans hL
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  intro p hpD R hR1 hR2 G hplain hirr hbal hord1 hord2 Dd hDd hlayers m u v hm hlad hdisj
    base roots boundary T0 hT0
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hlay : ∀ a, δ * ((Dd.layer a : ℝ) + 1) ≤ τ := by
    intro a
    have hpD' : p < D := hpD
    have h1 : Dd.layer a + 1 ≤ D := by have := hlayers a; omega
    have h2 : ((Dd.layer a : ℝ) + 1) ≤ (D : ℝ) := by exact_mod_cast h1
    rw [hτD]; nlinarith [hδ.1]
  have := ladder_L1_fixed (G := G) hd (γ := γ) (η := η) (δ := δ) (τ := τ) (x := x) (C0 := C0) (L := L)
    hγ0 hγ1 hx0 hx2 hC0 hδ.1 hδ.2 (by linarith) (hL1' L hLL1) hlad hplain Dd hDd hlay base roots boundary T0 hT0
  exact this

end WaveTurbulence.LadderDecay
