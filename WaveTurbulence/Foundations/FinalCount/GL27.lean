/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL26
/-! **G3-LOWDEG (R48), part 27: the pool `C₂` and `UnselOK` on `M.unloop`.**  The pool of `subpro` (4) of `M.unloop` is the image of
the pool of `M` under `Object.unloop` (an SG object avoids the loop atoms), so `C₂` and the DV selection correspond. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}
variable {R' : ℕ} {M : Molecule V D} {C : CollData M} {L γ η : ℝ} {w : Mom d} {κ : D → Fin d → ℤ}

/-- The image of a set of objects of `M` in `M.unloop`. -/
def unloopSet (M : Molecule V D) (Unsel : Set (Object M)) : Set (Object M.unloop) :=
  {B' | ∃ B ∈ Unsel, B' = B.unloop (Object.loopFree B)}

theorem InP_unloop (hC : LoopCtx L w κ R' M) (hH : HingeNoLoop C) (obl : SubproOblG C L γ η w κ) {B : Object M}
    (h : C.InP L γ η w κ B) : C.unloop.InP L γ η w (fun y : NonLoop M => κ y.1) (B.unloop (Object.loopFree B)) := by
  obtain ⟨hSG, hOut, hdis, -⟩ := h
  have hSG' := (Object.unloop_hasGapKind B (Object.loopFree B) L γ η w κ _).2 hSG
  have hOut' : C.unloop.Outside (B.unloop (Object.loopFree B)) := hOut
  exact ⟨hSG', hOut', hdis, (SubproOblG.unloop hC hH obl).contained _ hSG' hOut' hdis⟩

theorem InP_lift (hC : LoopCtx L w κ R' M) (obl : SubproOblG C L γ η w κ) {P : Object M.unloop}
    (h : C.unloop.InP L γ η w (fun y : NonLoop M => κ y.1) P) :
    C.InP L γ η w κ (P.lift (hC.noLoop γ η P h.1)) := by
  obtain ⟨hSG, hOut, hdis, -⟩ := h
  have hlf := hC.noLoop γ η P hSG
  have hSG' : (P.lift hlf).HasGapKind L γ η w κ .SG := (Object.lift_hasGapKind P hlf L γ η w κ _).2 hSG
  have hOut' : C.Outside (P.lift hlf) := hOut
  exact ⟨hSG', hOut', hdis, obl.contained _ hSG' hOut' hdis⟩

theorem Object.unloop_inj {P Q : Object M} (hP : LoopFreeSet M P.atoms) (hQ : LoopFreeSet M Q.atoms)
    (h : P.unloop hP = Q.unloop hQ) : P = Q := by
  have key : ∀ (X Y : Object M.unloop) (hX : LoopFreeSet M X.atoms) (hY : LoopFreeSet M Y.atoms), X = Y →
      X.lift hX = Y.lift hY := by
    rintro X Y hX hY rfl; rfl
  have := key _ _ (by exact hP) (by exact hQ) h
  exact (Object.lift_unloop P hP hP).symm.trans (this.trans (Object.lift_unloop Q hQ hQ))

theorem Object.unloop_shape_vc (U : Object M) (hU : LoopFreeSet M U.atoms) (h : ∃ h, U.shape = VineLikeObject.vc h) :
    ∃ h', (U.unloop hU).shape = VineLikeObject.vc h' := by
  obtain ⟨S, a, b, sh⟩ := U
  cases sh with
  | vc hv => exact ⟨_, rfl⟩
  | hyper R => obtain ⟨h, hh⟩ := h; cases hh

/-- A member of `C₂` of `M` maps to a member of `C₂` of `M.unloop`. -/
theorem C2Of_unloop {Unsel : Set (Object M)} (hC : LoopCtx L w κ R' M) (hH : HingeNoLoop C)
    (obl : SubproOblG C L γ η w κ) {U : Object M} (hUC : U ∈ C.C2Of L γ η w κ Unsel) :
    U.unloop (Object.loopFree U) ∈ C.unloop.C2Of L γ η w (fun y : NonLoop M => κ y.1) (unloopSet M Unsel) := by
  obtain ⟨⟨hUP, hUn⟩, hmax⟩ := hUC
  refine ⟨⟨InP_unloop hC hH obl hUP, ?_⟩, ?_⟩
  · rintro ⟨U₂, hU₂, he⟩
    exact hUn (by rwa [Object.unloop_inj _ _ he] )
  · rintro Q' ⟨hQP, hQn⟩ hsub
    have hlf := hC.noLoop γ η Q' hQP.1
    have hQ := InP_lift hC obl hQP
    have hQn' : Q'.lift hlf ∉ Unsel := fun hq => hQn ⟨_, hq, (Object.unloop_lift Q' hlf _).symm⟩
    exact hmax _ ⟨hQ, hQn'⟩ hsub

/-- Every member of `C₂` has a canonical member of `C₂` on the same atom set (R50 F-DESIG). -/
theorem CollData.exists_C2Can_of_C2Of {V' : Type*} [DecidableEq V'] {D' : Type*} [Fintype D'] [DecidableEq D']
    {M' : Molecule V' D'} (C' : CollData M') {κ' : D' → Fin d → ℤ} {Unsel : Set (Object M')} {U : Object M'}
    (hU : U ∈ C'.C2Of L γ η w κ' Unsel) : ∃ Q ∈ C'.C2Can L γ η w κ' Unsel, Q.atoms = U.atoms := by
  by_cases hh : ∃ R, U.shape = .hyper R
  · let S : Set ℕ := {n | ∃ Q ∈ C'.C2Of L γ η w κ' Unsel, Q.atoms = U.atoms ∧ (∃ R, Q.shape = .hyper R) ∧ Q.hyperRankG = n}
    have hne : ∃ n, n ∈ S := ⟨_, U, hU, rfl, hh, rfl⟩
    obtain ⟨Q, hQ, hQat, hQh, hQn⟩ := Nat.find_spec hne
    refine ⟨Q, ⟨hQ, fun Q' hQ' hat _ hQ'h => ?_⟩, hQat⟩
    have := Nat.find_min' hne (show Q'.hyperRankG ∈ S from ⟨Q', hQ', hat.trans hQat, hQ'h, rfl⟩)
    rw [hQn]; exact this
  · exact ⟨U, ⟨hU, fun _ _ _ h => absurd h hh⟩, rfl⟩

/-- **`UnselOK` on `M.unloop`** (session-19 form of the DV rule among the maximal objects: the unselected vine is covered by a
canonical member of `C₂`, or its DV partner is a VC member of the canonical `C₂`).  Re-based by FINALCOUNT-ASM session 20. -/
theorem UnselOK.unloop {Unsel : Set (Object M)} (hC : LoopCtx L w κ R' M) (hH : HingeNoLoop C)
    (obl : SubproOblG C L γ η w κ) (hU : C.UnselOK L γ η w κ Unsel) :
    C.unloop.UnselOK L γ η w (fun y : NonLoop M => κ y.1) (unloopSet M Unsel) where
  dv := by
    rintro B' ⟨B, hB, rfl⟩
    obtain ⟨hInP, hcase⟩ := hU.dv B hB
    refine ⟨InP_unloop hC hH obl hInP, ?_⟩
    rcases hcase with ⟨U, hUC, hsub⟩ | ⟨A, a, b, hA, hBv, hAB, U, hUC, hUA, hUs⟩
    · obtain ⟨Q, hQ, hQat⟩ := CollData.exists_C2Can_of_C2Of C.unloop (C2Of_unloop hC hH obl hUC.1)
      refine Or.inl ⟨Q, hQ, ?_⟩
      rw [hQat]
      exact hsub
    · have hlfA : LoopFreeSet M A := fun y hy => isVine_noLoop hA y hy
      have hlfB : LoopFreeSet M B.atoms := Object.loopFree B
      refine Or.inr ⟨A, a, b, ((unloopEmb M hlfA).isVine_iff rfl).1 hA,
        ((unloopEmb M hlfB).isVine_iff rfl).1 hBv, hAB, U.unloop (Object.loopFree U), ?_, hUA,
        Object.unloop_shape_vc U _ hUs⟩
      exact CollData.mem_C2Can_of_vc (C2Of_unloop hC hH obl hUC.1) (Object.unloop_shape_vc U _ hUs)

end WaveTurbulence.FinalCountG3
