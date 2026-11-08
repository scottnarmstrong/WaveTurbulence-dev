/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SpectralLinkParameters

/-! Ported by source from C2-B-TOP `Cut2BReg.SpectralLinkContinuity` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# Joint continuity of the computed spectral link factors

Fixed cell centers give a common finite lattice support. The Fourier
shifts are literal finite linear maps, so time and spectral variables
may be treated together in the ensuing measurable integral families.
-/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- Every computed spectral shift is an actual continuous finite linear expression. -/
@[fun_prop] theorem MomentumTreeData.continuous_spectralShiftSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (j : MomentumCoordinate n) :
    Continuous (fun ξ : LocalizedCellIndex n m → Fin d → ℝ => P.spectralShift ξ j) := by
  unfold spectralShift
  fun_prop

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Joint continuity of the literal analytic link factor in time and all Fourier variables. -/
theorem MomentumTreeData.continuous_spectral_linkTimeFactorSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : Fin n → LayerLink d) (z : (Fin n × Fin 2) → Fin d → ℤ) (i : Fin n) :
    Continuous (fun v : (Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      linkTimeFactor L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z v.2 i) v.1) := by
  classical
  let A := ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z 0 i).toLinkParameters
  let S := (finite_support_linkAmplitude hL A).toFinset
  have ha (ξ : LocalizedCellIndex n m → Fin d → ℝ) (p : (Fin d → ℤ) × (Fin d → ℤ)) :
      linkAmplitude L ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ i).toLinkParameters p = linkAmplitude L A p := rfl
  have he : (fun v : (Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ) =>
      linkTimeFactor L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z v.2 i) v.1) =
      fun v => ∑ p ∈ S, linkAmplitude L A p *
        WeylSums.e (linkPhase L ((((Q i).orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) *
          (v.1 0 - v.1 1)) ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z v.2 i).toLinkParameters p) := by
    funext v
    unfold linkTimeFactor linkLatticeSum
    simp_rw [ha]
    apply tsum_eq_sum
    intro p hp
    have hz : linkAmplitude L A p = 0 := by
      by_contra hn
      exact hp (by simpa only [S, Set.Finite.mem_toFinset, Function.mem_support] using hn)
    rw [hz, zero_mul]
  rw [he]
  apply continuous_finsetSum
  intro p _
  unfold linkPhase WeylSums.e spectralLinksSpatial
  fun_prop

end WaveTurbulence.Flower.IncTop