/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.DegenVinePar.MixSumint
public import WaveTurbulence.Foundations.SumintPar.Sumint

/-! # `sumint` for character-mixture multiplied sums, in the prefix form (DEGEN-VINE)

`sumintMix` is `SumintPar.sumint` with the lattice sum weighted by a character mixture `M` (mass `K`);
the right-hand side is multiplied by `K`.  `sumintMixSigned` is the form for the snapshot-9 datum with the
core signs (`VineEstS2.signedPhase`), transported along the field-by-field copy `SumintPar.ofOrig`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.DegenVinePar
open WaveTurbulence.DegenVine
open WaveTurbulence.SumintPar MeasureTheory Set
open scoped ENNReal

/-- `sumint` (parametric weights) with a character-mixture multiplier, prefix form. -/
def SumintMixPar : Prop := WTPrefixA fun A P =>
    ∀ (D : SumintPar.SumintDatum P.d) (hI : 0 < D.S.I), D.Admissible A P.L P.γ P.η P.D →
      D.S.M ≤ P.N 1 ^ 4 → ∀ M : CharMix D.S P.d,
      let B : Set (Fin 3 → ℝ) := {tt | (∀ c, (D.qOut c : ℝ) ≤ tt c ∧ tt c ≤ D.qOut c + 1) ∧
        max (tt 1) (tt 2) < tt 0}
      let K : Set (Fin 4 → Mom P.d) := {v | (∀ c, (∃ nv : Fin P.d → ℤ, v c = D.wBar +
          latticePoint P.L nv) ∧ ‖v c - D.centre c‖ ≤ 1) ∧ v 0 - v 1 = v 3 - v 2 ∧ v 0 ≠ v 1 ∧
        ‖v 0 - v 1‖ ≤ P.L ^ (-P.γ + P.η)}
      let maxPar : ℝ := ⨆ v, jbr (d := 1) (WithLp.toLp 2 fun _ => D.param v)
      XNorm00Restr (2 * P.η ^ 8) B K (fun tt v => exprMix M hI P.L P.γ P.δ P.η tt v) ≤
        ENNReal.ofReal (M.mass * (P.C₁ * maxPar ^ (P.η ^ 6) * (P.C₁ * P.δ ^ (-(1 : ℝ) / 2)) ^ D.S.M *
          P.L ^ ((D.S.M : ℝ) * (P.d - P.γ) -
            P.η ^ 2 * ((Finset.univ.filter fun i => D.S.nor i = false).card + D.M₁) -
            P.η ^ 8 * D.M₀ + P.η ^ 7)))

theorem sumintMix : SumintMixPar := by
  unfold SumintMixPar
  intro d hd γ hγ
  obtain ⟨η0,hη0,hsmall⟩ := exists_sumintSmallness_threshold d hd γ hγ
  refine ⟨η0,hη0,?_⟩
  intro η hη A hA φin hφin τstar hτstar φ hφ
  obtain ⟨C1,hC1,hbound⟩ := exists_mix_sumint_bound d hd γ hγ η (hsmall η hη) A hA τstar hτstar
  refine ⟨C1,hC1,1,by norm_num,?_⟩
  intro ν hν
  refine ⟨1/16,by norm_num,?_⟩
  intro δ hδ N hN hτ
  obtain ⟨R,hR,hbound⟩ := hbound δ N hδ hτ
  refine ⟨1,by norm_num,R,hR,?_⟩
  intro L hL D hI hD hsize M
  simpa only [sourceOutputTimeSet,sourceOutputSet,parameterMaximum,sourceTargetExponent,Nat.cast_add]
    using hbound L hL D hI hD M

end WaveTurbulence.DegenVinePar
