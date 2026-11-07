/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.AssemblyClocked
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSumintAlgebraicHypotheses
public import WaveTurbulence.Foundations.VineEst.VineEstS3.ScaledSumint

/-! # `Admissible` for the source datum (Step 3): the param-generic form required by the engine

`BadClause D` is the bad-case clause of `SumintDatum.Admissible` (cases (a) and (d); TARGET L1607-L1622).
`admissible_source`: for every parameter vector and every weight pair obeying `WeightBounds`, the datum
`{sourceSumintDatum .. W with param := p, wK := a, wL := b}` is `Admissible` for `A ≥ 6561`, given the layer bounds
`q + 1 ≤ 𝔇` and the bad-case clause: the algebraic clauses are `sourceSumintDatum_algebraic_hypotheses`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng VineParamContract RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The bad-case clause of `Admissible` (cases (a), (c)-nonvacuity and (d)). -/
def BadClause (D : SumintDatum d) : Prop :=
  ∀ i, D.S.nor i = false →
    (D.badKind i = 0 → ∃ h : 0 < D.S.m i,
      let t0 : D.S.TVar := .inl ⟨i, 0⟩
      let t1 : D.S.TVar := .inl ⟨i, ⟨1, by omega⟩⟩
      let s1 : D.S.TVar := .inr (.inl ⟨i, ⟨0, h⟩⟩)
      ((s1, t0) ∈ D.constraints ∧ (t0, t1) ∈ D.constraints) ∨
        ((t1, t0) ∈ D.constraints ∧ (t0, s1) ∈ D.constraints)) ∧
    (D.badKind i = 2 → 0 < D.S.m i) ∧
    (D.badKind i = 3 → ∃ j : Fin (D.S.n i), 1 ≤ max (D.g ⟨i, j⟩) (D.g' ⟨i, j⟩))

theorem admissible_source (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) {A L γ η : ℝ} (hA : 6561 ≤ A) {Dsteps : ℕ}
    (hq : ∀ v, W.q v + 1 ≤ Dsteps) (hqo : ∀ c, W.qOut c + 1 ≤ Dsteps)
    (hbad : BadClause (sourceSumintDatum hM9 B hG W)) :
    ∀ (p : (sourceSumintDatum hM9 B hG W).S.TVar → ℝ) (a b : (sourceSumintDatum hM9 B hG W).S.VIdx → Mom d → ℂ),
      WeightBounds (sourceSumintDatum hM9 B hG W) L γ η a b →
      ({ sourceSumintDatum hM9 B hG W with param := p, wK := a, wL := b } : SumintDatum d).Admissible A L γ η Dsteps := by
  intro p a b hwb
  have halg := sourceSumintDatum_algebraic_hypotheses hM9 B hG
    { W with param := p, wK := a, wL := b }
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := halg
  refine ⟨h1, h2, ?_, ?_, ?_, h5, h6, hq, hqo, hbad⟩
  · refine h3.trans ?_
    exact pow_le_pow_left₀ (by norm_num) hA _
  · intro v
    obtain ⟨p', q', hT, hH⟩ := h4 v
    refine ⟨p', q', ?_⟩
    dsimp only
    constructor
    · intro j
      rcases p' with p' | p' | p' <;> rcases q' with q' | q' | q' <;> exact hT j
    · intro c
      rcases p' with p' | p' | p' <;> rcases q' with q' | q' | q' <;> exact hH c
  · intro v
    exact hwb v

end WaveTurbulence.VineEstS3
