/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowGardenLift
/-! **FINALCOUNT-ASSEMBLY (LOW-GARDEN, session 2): `LowClassHyps2` on `M.unloop`.**

`lowClassHyps2_unloop`: from the data on a molecule `M` with at least one loop (the `LowLoopData` of the garden-level facts of the
REG producers, which hold with loops) every field of `LowClassHyps2` holds on `M.unloop` with index `R + k`, collection
`C.unloop`, omitted vines `unloopSet`, first-stage set `unloopSet M Fst`, for every nonempty class of `unloopAdm M Adm`.
The new `degen` field `DegenSGTL`: an atom with a loop and a zero-gap pair on `M.unloop` has degree 2, equal labels (`heq`), so
it is a `SmoothAt` atom; atoms without a loop keep their degree, so `M`-tame is `M.unloop`-tame. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.VineCount

section gen
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

theorem sourceLadderGaps_unloop {M : Molecule V D} {L : ℝ} {w : Mom d} {P : Finset V → ℝ} {κ : D → Fin d → ℤ}
    (h : SourceLadderGaps M L w P κ) : SourceLadderGaps M.unloop L w P (fun y : NonLoop M => κ y.1) := by
  intro S hS
  rw [unloop_maximalLadders] at hS
  obtain ⟨hP, m, u, v, hm, hl, hS2, r, hr, h0, h1, h2⟩ := h S hS
  refine ⟨hP, m, u, v, hm, (unloop_isLadder M u v).2 hl, hS2, r, ?_, h0, h1, h2⟩
  obtain ⟨x, y, hx, hy, hax, hay, hrr⟩ := hr
  have hinj := hl.2.1
  have hu01 : u 0 ≠ u ⟨1, by omega⟩ := fun e => by
    have := @hinj (Sum.inl 0) (Sum.inl ⟨1, by omega⟩) (by simpa using e)
    simp [Fin.ext_iff] at this
  have hv01 : v 0 ≠ v ⟨1, by omega⟩ := fun e => by
    have := @hinj (Sum.inr 0) (Sum.inr ⟨1, by omega⟩) (by simpa using e)
    simp [Fin.ext_iff] at this
  exact ⟨⟨x, ends_ne_of hu01 hx⟩, ⟨y, ends_ne_of hv01 hy⟩, hx, hy, hax, hay, hrr⟩

theorem lift_shape_vc {M : Molecule V D} (P' : Object M.unloop) (hlf : LoopFreeSet M P'.atoms)
    (h : ∃ h, P'.shape = VineLikeObject.vc h) : ∃ h, (P'.lift hlf).shape = VineLikeObject.vc h := by
  obtain ⟨S, a, b, sh⟩ := P'
  cases sh with
  | vc hv => exact ⟨_, rfl⟩
  | hyper R => obtain ⟨h, hh⟩ := h; cases hh

theorem unloop_shape_vc' {M : Molecule V D} (U : Object M) (hU : LoopFreeSet M U.atoms)
    (h : ∃ h, (U.unloop hU).shape = VineLikeObject.vc h) : ∃ h, U.shape = VineLikeObject.vc h := by
  obtain ⟨S, a, b, sh⟩ := U
  cases sh with
  | vc hv => exact ⟨_, rfl⟩
  | hyper R => obtain ⟨h, hh⟩ := h; cases hh

end gen

end WaveTurbulence.FinalCountAsm
