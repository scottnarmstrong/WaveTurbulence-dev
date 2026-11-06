/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SpecFacts
public import WaveTurbulence.Foundations.Molecule.GardenIncidence
import Mathlib.Tactic
/-! Counting the values of `α_v` (TARGET L2025–L2026: `Γ_v` takes at most `L^{20d}` values). -/
@[expose] public section
open WaveTurbulence.Induct
open Finset
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LGSpine

theorem exists_lattice_box {d : ℕ} (L : ℝ) (hL : 0 < L) (base c : Mom d) :
    ∃ B : Finset (Fin d → ℤ), (∀ κ : Fin d → ℤ, ‖base + latticePoint L κ - c‖ ≤ 1 → κ ∈ B) ∧
      B.card ≤ (⌊2 * L⌋₊ + 1) ^ d := by
  classical
  let t : Fin d → ℝ := fun i => L * (c i - base i)
  refine ⟨Fintype.piFinset (fun i => Finset.Icc ⌈t i - L⌉ ⌊t i + L⌋), ?_, ?_⟩
  · intro κ hκ
    rw [Fintype.mem_piFinset]
    intro i
    have h1 : |(base + latticePoint L κ - c) i| ≤ ‖base + latticePoint L κ - c‖ := by
      simpa using PiLp.norm_apply_le (base + latticePoint L κ - c) i
    have h2 : (base + latticePoint L κ - c) i = base i + (κ i : ℝ) / L - c i := by
      simp [latticePoint]
    rw [h2] at h1
    have h3 := abs_le.mp (h1.trans hκ)
    rw [Finset.mem_Icc]
    constructor
    · rw [Int.ceil_le]
      have : t i - L ≤ κ i := by
        have := h3.1
        have h4 : (κ i : ℝ) / L ≥ c i - base i - 1 := by linarith
        have h5 : (κ i : ℝ) ≥ L * (c i - base i - 1) := by
          have := (le_div_iff₀ hL).mp (show c i - base i - 1 ≤ (κ i : ℝ) / L by linarith)
          linarith
        simp only [t]; nlinarith
      exact this
    · rw [Int.le_floor]
      have h5 : (κ i : ℝ) ≤ L * (c i - base i + 1) := by
        have := (div_le_iff₀ hL).mp (show (κ i : ℝ) / L ≤ c i - base i + 1 by linarith [h3.2])
        linarith
      simp only [t]; nlinarith
  · rw [Fintype.card_piFinset]
    calc ∏ i : Fin d, (Finset.Icc ⌈t i - L⌉ ⌊t i + L⌋).card ≤ ∏ _i : Fin d, (⌊2 * L⌋₊ + 1) := by
          refine Finset.prod_le_prod' (fun i _ => ?_)
          rw [Int.card_Icc]
          have h1 : ((⌊t i + L⌋ - ⌈t i - L⌉ : ℤ) : ℝ) ≤ 2 * L := by
            have := Int.floor_le (t i + L)
            have := Int.le_ceil (t i - L)
            push_cast; linarith
          have h2 : ⌊t i + L⌋ - ⌈t i - L⌉ ≤ ⌊2 * L⌋ := by
            exact Int.le_floor.mpr h1
          have h3 : ⌊2 * L⌋ = (⌊2 * L⌋₊ : ℤ) := by
            rw [Int.natCast_floor_eq_floor (by positivity)]
          omega
      _ = (⌊2 * L⌋₊ + 1) ^ d := by simp

theorem exists_value_finset {w d : ℕ} (G : Garden w) (hp : G.IsPlain) {L : ℝ} (hL : 0 < L)
    (D : SplicedKernelData G d) (hamp : SplicedAmplitudeBounds G D)
    (scales : Finset (GBranch G.tree) → ℝ) (γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (v : GBranch G.tree) :
    ∃ F : Finset ℝ, (∀ α ∈ splicedFrequencySpectrum G D scales L γ η δ base roots, α v ∈ F) ∧
      F.card ≤ (⌊2 * L⌋₊ + 1) ^ (4 * d) := by
  classical
  choose B hB hBc using fun x : GardenDart G => exists_lattice_box L hL base (D.center x)
  let g : ({x // x ∈ G.molecule.dartsAt v} → (Fin d → ℤ)) → ℝ := fun κ' =>
    δ * L ^ (2 * γ) * (- ∑ x : {x // x ∈ G.molecule.dartsAt v},
        G.molecule.dartSign x.1 * ‖base + latticePoint L (κ' x)‖ ^ 2 +
      Mole.gardenSource G hp (fun i => ‖base + latticePoint L (roots i)‖ ^ 2) v) + D.frequency v
  refine ⟨(Fintype.piFinset (fun x : {x // x ∈ G.molecule.dartsAt v} => B x.1)).image g, ?_, ?_⟩
  · rintro α ⟨z, _, _, hb, _, rfl⟩
    have hL0 : L ≠ 0 := hL.ne'
    have hdec := spliced_molecule_decoration G hp hL0 base roots z
    rw [Finset.mem_image]
    refine ⟨fun x => bondIndex G z.1 x.1, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro x
      apply hB
      have := dart_near_center G D hamp L base (bondIndex G z.1) hdec.1 hb x.1
      simpa [Molecule.kvec] using this
    · rw [splicedFrequency_eq G hp hL0 D γ δ base roots z v]
      simp only [g, Molecule.Gamma, Molecule.kvec]
      have hs := Finset.sum_coe_sort (G.molecule.dartsAt v)
        (fun x => G.molecule.dartSign x * ‖base + latticePoint L (bondIndex G z.1 x)‖ ^ 2)
      rw [hs]
  · refine (Finset.card_image_le).trans ?_
    rw [Fintype.card_piFinset]
    have hd : (G.molecule.dartsAt v).card ≤ 4 := WaveTurbulence.Mole.garden_molecule_deg_le_four G v
    calc ∏ x : {x // x ∈ G.molecule.dartsAt v}, (B x.1).card
        ≤ ∏ _x : {x // x ∈ G.molecule.dartsAt v}, (⌊2 * L⌋₊ + 1) ^ d :=
          Finset.prod_le_prod' (fun x _ => hBc x.1)
      _ = ((⌊2 * L⌋₊ + 1) ^ d) ^ (G.molecule.dartsAt v).card := by simp
      _ ≤ ((⌊2 * L⌋₊ + 1) ^ d) ^ 4 :=
          Nat.pow_le_pow_right (Nat.one_le_pow _ _ (Nat.succ_pos _)) hd
      _ = _ := by rw [← pow_mul]; ring_nf

end WaveTurbulence.Ladder
