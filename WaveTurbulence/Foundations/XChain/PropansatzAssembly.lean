/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.PrefixInduction
public import WaveTurbulence.Foundations.XChain.PrefixAlignment
public import WaveTurbulence.Foundations.XChain.SmallDeltaChoice
/-! Conditional assembly of the exact snapshot-5 propansatz from precisely the three source gates. -/
public section
namespace WaveTurbulence.Induct
open Set
universe u

theorem propansatz_of_gates (hLayergarden : LayergardenGate) (hFixedpoint : FixedpointGate.{u})
    (hWkeTaylor : WkeTaylorGate) : PropansatzGate.{u} := by
  have hcommon := gates_common_prefix hLayergarden hFixedpoint hWkeTaylor
  intro d hd γ hγ
  obtain ⟨η0, hη0, kη⟩ := hcommon d hd γ hγ
  refine ⟨η0, hη0, ?_⟩
  intro η hη φin hφin τstar hτ φ hsol
  obtain ⟨C1, hC1, ν0, hν0, kν⟩ := kη η hη φin hφin τstar hτ φ hsol
  refine ⟨C1, hC1, ν0, hν0, ?_⟩
  intro ν hν
  obtain ⟨δgate, hδgate, kδ⟩ := kν ν hν
  let δ0 := min δgate (min 1 (min (Real.exp (-8000000 / ν)) (Real.exp (-1) / C1)))
  have hC1pos : 0 < C1 := zero_lt_one.trans_le hC1
  have hδ0 : 0 < δ0 := lt_min hδgate (lt_min zero_lt_one
    (lt_min (Real.exp_pos _) (div_pos (Real.exp_pos _) hC1pos)))
  refine ⟨δ0, hδ0, ?_⟩
  intro δ hδ D hD htime
  have hδparts : δ ≤ δgate ∧ δ ≤ 1 ∧ δ ≤ Real.exp (-8000000 / ν) ∧ δ ≤ Real.exp (-1) / C1 := by
    simpa only [δ0, le_min_iff] using hδ.2
  obtain ⟨C2, hC2, Lgate, hLgate, kL⟩ := kδ δ ⟨hδ.1, hδparts.1⟩ D hD htime
  let P0 : WTParams := ⟨d, γ, η, φin, τstar, φ, C1, ν, δ, D, C2, 1⟩
  obtain ⟨B, hB, hφ⟩ := uniform_schwartz_bracket_bound τstar φ hsol.1 (4 * P0.Lambda 0)
  let Cmom := ⌈B + 4⌉₊
  let L0 := max Lgate (max 2 (assemblySizeThreshold P0 (B + 1) Cmom))
  refine ⟨C2, hC2, L0, (le_max_left _ _).trans (le_max_right _ _), ?_⟩
  intro L hL
  obtain ⟨hGarden, hFixed, hTaylor⟩ := kL L ((le_max_left _ _).trans hL)
  let P : WTParams := ⟨d, γ, η, φin, τstar, φ, C1, ν, δ, D, C2, L⟩
  apply propansatz_body_of_context (P := P)
  refine ⟨by change 1 ≤ d; omega, hη.1, hδ.1, hδparts.2.1, hν.1.le, ?_,
    zero_le_one.trans hC1, zero_le_one.trans hC2, ?_, hφin, hsol,
    hGarden, hFixed, hTaylor, B, hB, ?_, Cmom, Nat.le_ceil (B + 4), ?_,
    delta_half_power_le_of_threshold hδ.1 hν.1 hδparts.2.2.1, ?_⟩
  · have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    exact hγ.2.le.trans (by linarith)
  · change δ * D ≤ τstar
    rw [htime]
    exact le_of_eq (mul_comm _ _)
  · simpa only [P, P0, WTParams.Lambda, Nat.sub_zero, Nat.cast_mul, Nat.cast_ofNat] using hφ
  · change assemblySizeThreshold P0 (B + 1) Cmom ≤ L
    exact (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  · have hh : δ * C1 ≤ Real.exp (-1) := (le_div_iff₀ hC1pos).mp hδparts.2.2.2
    simpa only [mul_comm] using hh

end WaveTurbulence.Induct
