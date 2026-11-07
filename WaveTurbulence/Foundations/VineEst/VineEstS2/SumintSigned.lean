/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.SumintDatum

public import WaveTurbulence.Frozen.Defs.SumintDatumAdmissible

public import WaveTurbulence.Frozen.Defs.SumintDatumEllVec

public import WaveTurbulence.Frozen.Defs.SumintDatumExpr

public import WaveTurbulence.Frozen.Defs.SumintDatumKVec

public import WaveTurbulence.Frozen.Defs.SumintDatumM0

public import WaveTurbulence.Frozen.Defs.SumintDatumM1

public import WaveTurbulence.Frozen.Defs.SumintDatumPhase

public import WaveTurbulence.Frozen.Defs.SumintDatumTimeDom

public import WaveTurbulence.Frozen.Defs.SumintShape

public import WaveTurbulence.Frozen.Defs.SumintShapeLexLt

public import WaveTurbulence.Frozen.Defs.SumintShapeM

public import WaveTurbulence.Frozen.Defs.SumintShapeN

public import WaveTurbulence.Frozen.Defs.SumintShapeTVar

public import WaveTurbulence.Frozen.Defs.SumintShapeUSlot

public import WaveTurbulence.Frozen.Defs.SumintShapeVIdx

public import WaveTurbulence.Frozen.Defs.SumintShapeX0Slot

public import WaveTurbulence.Frozen.Defs.SumintShapeXSlot

public import WaveTurbulence.Frozen.Defs.SumintShapeYSlot

public import WaveTurbulence.Frozen.Defs.WTPrefixA

public import WaveTurbulence.Frozen.Defs.EpsCoef

public import WaveTurbulence.Foundations.WaveB.FrozenB1

/-! # Owner-authorized signed sumint obligation (F79)

The snapshot-9 B1.6 statement is unchanged except for a common core sign and a relative sign on the nonlinear
core alternative. This is an explicit external named obligation, authorized by
the orchestrator for V4; no proof of it or change to B1.6 is asserted here.
The constant remains uniform in the core signs. All other hypotheses, domains,
weights, parameters, exponents and prefix quantifiers are copied verbatim.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open MeasureTheory Finset Set
open scoped ENNReal

noncomputable def signedPhase {d : ℕ} (D : SumintDatum d) (coreFirstSign coreSign : Fin D.S.I → ℤˣ) (L γ δ η : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (r : Mom d) (t : ℝ)
    (τ : D.S.TVar → ℝ) : ℂ :=
  let c := δ * L ^ (2 * γ)
  let X : D.S.VIdx → Mom d := fun v => latticePoint L (x v)
  let e (θ : ℝ) : ℂ := Complex.exp ((Real.pi * θ : ℝ) * Complex.I)
  (∏ i, ((∏ j : Fin (D.S.m i), e (c * (τ (.inl ⟨i, j.succ⟩) - τ (.inr (.inl ⟨i, j⟩))) *
        inner ℝ (X (D.S.xSlot i j)) (X (D.S.ySlot i j)))) *
      e (c * (τ (.inl ⟨i, 0⟩) - t) * inner ℝ r (X (D.S.x0Slot i))) *
      (∏ j : Fin (D.S.m i), e (c * (τ (.inl ⟨i, j.succ⟩) - t) * inner ℝ r
        ((D.ζc i j 0 : ℝ) • X (D.S.xSlot i j) + (D.ζc i j 1 : ℝ) • X (D.S.ySlot i j) +
          (D.ζc i j 2 : ℝ) • r))) *
      (∏ j : Fin (D.S.m i + 1), e (D.param (.inl ⟨i, j⟩) * τ (.inl ⟨i, j⟩))) *
      (∏ j : Fin (D.S.m i), e (D.param (.inr (.inl ⟨i, j⟩)) * τ (.inr (.inl ⟨i, j⟩)))) *
      (if h : D.S.nor i = false ∧ D.badKind i = 2 ∧ 0 < D.S.m i then
        ((|τ (.inl ⟨i, ⟨1, by omega⟩⟩) - τ (.inr (.inl ⟨i, ⟨0, h.2.2⟩⟩))| ^ (1 - 3 * η) : ℝ) : ℂ)
      else 1))) *
  ∏ i : {i : Fin D.S.I // D.S.nor i = true},
    let u (c' : Fin 3) := X (D.S.uSlot i.1 i.2 c')
    let τ' (c' : Fin 3) := τ (.inr (.inr ⟨i, c'⟩))
    e (c * (τ' 0 - τ' 2) * (((coreFirstSign i.1 : ℤ) : ℝ) * inner ℝ (u 0) (u 1))) *
      e (c * (τ' 1 - τ' 2) * (((coreFirstSign i.1 : ℤ) : ℝ) *
        (if D.Λsel i.1 then inner ℝ (u 0) (u 2) else (((coreSign i.1 : ℤ) : ℝ) * inner ℝ (u 2) (u 0 + u 1 - u 2))))) *
      e (c * (τ' 2 - t) * inner ℝ r ((D.ξc i.1 0 : ℝ) • u 0 + (D.ξc i.1 1 : ℝ) • u 1 +
        (D.ξc i.1 2 : ℝ) • u 2 + (D.ξc i.1 3 : ℝ) • r)) *
      ∏ c', e (D.param (.inr (.inr ⟨i, c'⟩)) * τ' c')

noncomputable def signedExpr {d : ℕ} (D : SumintDatum d) (coreFirstSign coreSign : Fin D.S.I → ℤˣ) (hI : 0 < D.S.I) (L γ δ η : ℝ) (tt : Fin 3 → ℝ) (efgh : Fin 4 → Mom d) :
    ℂ :=
  let r := efgh 0 - efgh 1
  ((‖r‖ ^ (Finset.univ.filter fun i => D.S.nor i = false ∧ D.badKind i = 1).card : ℝ) : ℂ) *
  ∑' x : D.S.VIdx → (Fin d → ℤ),
    (∏ v, D.wK v (D.kVec L x efgh v) * D.wL v (D.ℓVec L x efgh v)) *
      ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2), signedPhase D coreFirstSign coreSign L γ δ η x r (tt 0) τ

/-- Exact named obligation requested by the orchestrator for F79. -/
def SumintSigned : Prop := WTPrefixA fun A P =>
    ∀ (D : SumintDatum P.d) (hI : 0 < D.S.I) (coreFirstSign coreSign : Fin D.S.I → ℤˣ), D.Admissible A P.L P.γ P.η P.D →
      D.S.M ≤ P.N 1 ^ 4 →
      let B : Set (Fin 3 → ℝ) := {tt | (∀ c, (D.qOut c : ℝ) ≤ tt c ∧ tt c ≤ D.qOut c + 1) ∧
        max (tt 1) (tt 2) < tt 0}
      let K : Set (Fin 4 → Mom P.d) := {v | (∀ c, (∃ nv : Fin P.d → ℤ, v c = D.wBar +
          latticePoint P.L nv) ∧ ‖v c - D.centre c‖ ≤ 1) ∧ v 0 - v 1 = v 3 - v 2 ∧ v 0 ≠ v 1 ∧
        ‖v 0 - v 1‖ ≤ P.L ^ (-P.γ + P.η)}
      let maxPar : ℝ := ⨆ v, jbr (d := 1) (WithLp.toLp 2 fun _ => D.param v)
      XNorm00Restr (2 * P.η ^ 8) B K (fun tt v => signedExpr D coreFirstSign coreSign hI P.L P.γ P.δ P.η tt v) ≤
        ENNReal.ofReal (P.C₁ * maxPar ^ (P.η ^ 6) * (P.C₁ * P.δ ^ (-(1 : ℝ) / 2)) ^ D.S.M *
          P.L ^ ((D.S.M : ℝ) * (P.d - P.γ) -
            P.η ^ 2 * ((Finset.univ.filter fun i => D.S.nor i = false).card + D.M₁) -
            P.η ^ 8 * D.M₀ + P.η ^ 7))

end WaveTurbulence.VineEstS2
