/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.V2Chain.PrefixS
public import WaveTurbulence.Foundations.XChain.PropansatzAssembly

/-!
# V2-CHAIN: INDUCT's `propansatz_of_gates` with `γ` restricted to `S`

`Induct.gates_common_prefix` and `Induct.propansatz_of_gates` re-stated for `WTPrefixS S`. The proofs are the
originals, except that `hS : γ ∈ S` is passed to the three gates. Nothing else uses `γ`.
-/

@[expose] public section

namespace WaveTurbulence.V2Chain

open WaveTurbulence WaveTurbulence.Induct Set

universe u

variable {S : Set ℝ}


/-- The independent existential constants in the three source gates can be aligned.
C₁ and C₂ are taken from wkeTaylor; the other two assertions do not use them. -/
theorem gatesS_common_prefix (hL : WTPrefixS S LayergardenBody) (hF : WTPrefixS S FixedpointBody.{u})
    (hW : WTPrefixS S WkeTaylorBody) :
    WTPrefixS S (fun P => LayergardenBody P ∧ FixedpointBody.{u} P ∧ WkeTaylorBody P) := by
  intro d hd γ hγ hS
  obtain ⟨ηL, hηL, kL⟩ := hL d hd γ hγ hS
  obtain ⟨ηF, hηF, kF⟩ := hF d hd γ hγ hS
  obtain ⟨ηW, hηW, kW⟩ := hW d hd γ hγ hS
  let η₀ := min ηL (min ηF ηW)
  refine ⟨η₀, lt_min hηL (lt_min hηF hηW), ?_⟩
  intro η hη φin hφ τstar hτ φ hsol
  have hηall : η ≤ ηL ∧ η ≤ ηF ∧ η ≤ ηW := by
    simpa only [η₀, le_min_iff] using hη.2
  obtain ⟨CL, _, νL, hνL, rL⟩ := kL η ⟨hη.1, hηall.1⟩ φin hφ τstar hτ φ hsol
  obtain ⟨CF, _, νF, hνF, rF⟩ := kF η ⟨hη.1, hηall.2.1⟩ φin hφ τstar hτ φ hsol
  obtain ⟨CW, hCW, νW, hνW, rW⟩ := kW η ⟨hη.1, hηall.2.2⟩ φin hφ τstar hτ φ hsol
  let ν₀ := min νL (min νF νW)
  refine ⟨CW, hCW, ν₀, lt_min hνL (lt_min hνF hνW), ?_⟩
  intro ν hν
  have hνall : ν ≤ νL ∧ ν ≤ νF ∧ ν ≤ νW := by
    simpa only [ν₀, le_min_iff] using hν.2
  obtain ⟨δL, hδL, sL⟩ := rL ν ⟨hν.1, hνall.1⟩
  obtain ⟨δF, hδF, sF⟩ := rF ν ⟨hν.1, hνall.2.1⟩
  obtain ⟨δW, hδW, sW⟩ := rW ν ⟨hν.1, hνall.2.2⟩
  let δ₀ := min δL (min δF δW)
  refine ⟨δ₀, lt_min hδL (lt_min hδF hδW), ?_⟩
  intro δ hδ D hD htime
  have hδall : δ ≤ δL ∧ δ ≤ δF ∧ δ ≤ δW := by
    simpa only [δ₀, le_min_iff] using hδ.2
  obtain ⟨C₂L, _, LL, hLL, tL⟩ := sL δ ⟨hδ.1, hδall.1⟩ D hD htime
  obtain ⟨C₂F, _, LF, hLF, tF⟩ := sF δ ⟨hδ.1, hδall.2.1⟩ D hD htime
  obtain ⟨C₂W, hC₂W, LW, hLW, tW⟩ := sW δ ⟨hδ.1, hδall.2.2⟩ D hD htime
  let L₀ := max LL (max LF LW)
  refine ⟨C₂W, hC₂W, L₀, hLL.trans (le_max_left _ _), ?_⟩
  intro L hsize
  have hsizeall : LL ≤ L ∧ LF ≤ L ∧ LW ≤ L := by
    simpa only [L₀, max_le_iff] using hsize
  let PL : WTParams := ⟨d, γ, η, φin, τstar, φ, CL, ν, δ, D, C₂L, L⟩
  let PF : WTParams := ⟨d, γ, η, φin, τstar, φ, CF, ν, δ, D, C₂F, L⟩
  refine ⟨?_, ?_, tW L hsizeall.2.2⟩
  · change LayergardenBody {PL with C₁ := CW, C₂ := C₂W}
    rw [layergardenBody_update_aux]
    exact tL L hsizeall.1
  · change FixedpointBody.{u} {PF with C₁ := CW, C₂ := C₂W}
    rw [fixedpointBody_update_aux]
    exact tF L hsizeall.2.1


theorem propansatzS_of_gates (hLayergarden : WTPrefixS S LayergardenBody)
    (hFixedpoint : WTPrefixS S FixedpointBody.{u}) (hWkeTaylor : WTPrefixS S WkeTaylorBody) :
    WTPrefixS S PropansatzBody.{u} := by
  have hcommon := gatesS_common_prefix hLayergarden hFixedpoint hWkeTaylor
  intro d hd γ hγ hS
  obtain ⟨η0, hη0, kη⟩ := hcommon d hd γ hγ hS
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


end WaveTurbulence.V2Chain
