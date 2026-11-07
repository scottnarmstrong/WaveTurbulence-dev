/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.Free
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.Glue
public import WaveTurbulence.Foundations.VineEst.VineEstS2.VineChainSumintForm

/-! # P4-W2 (N2): the free-domain dictionary from the row form

**N2(a), the phase.**  `engDatum_phase`: the phase of the engine datum `engDatum hM9 B hG W ..` (P2) is the `signedPhase` of the
source datum with the parameters and the bad kinds switched off (`W0 W`), times the parameter factor `paramFac W.param τ`
(`∏_v e^{πi p_v τ_v}`) and the kind-2 factor `k2c bk η τ` (`∏_i |t₁ⁱ - s₁ⁱ|^{1-3η}` over the kind-2 blocks).  With the R58 modulation
(the parameter `λ` at the clock of the lower joint `b`, `W.param = λ · 1_{v₀}`, `v₀ = t₀⁰` = `.inl ⟨⟨0, hI⟩, 0⟩`) the parameter factor is
`e^{πiλτ_b}` (`paramFac_single`, `clock_lowerJoint`).  The recentring factor `recFac` and the regional phase combine into the
`signedPhase` (`recFac_mul_regionalPhase`: `clLocalDecoration_phase_recenter`, then `assembly_regionalPhase_eq_signedPhase`).

**`freeDict_of_rowForm`.**  For a summand `ψ = e^{πiλu_b} ψ₀` with `ψ₀` in row form (`RowForm R ψ₀ Dm Qw Tw`, N1), the free-domain
dictionary `FreeDict` holds as soon as
* (`hMx`) the character mixture is the sign `ε` of the decoration,
* (`hsub`) a.e. on the engine time domain the row-form time condition holds, (`hvan`) a.e. where the row-form condition holds outside
  the engine domain the product of the row weights vanishes (the clock indicators of the twin-ordered pieces sit in their rows), and
* (`hrow`) a.e. on the engine time domain, the product of the row-form weights is `kind1Pref · k2c · ∏_ρ (engine row ρ)`.
The row matching (`hrow`, N2(b)) and the time domain (`hsub`, `hvan`, N2(c)) are separate modules.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
variable {kind : Bool}
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
open scoped ENNReal

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The weight/clock data with the parameters and the bad kinds switched off. -/
def W0 {S : WaveTurbulence.SumintShape} (W : SumintWeightClockData S d) : SumintWeightClockData S d :=
  { W with param := fun _ => 0, badKind := fun _ => 0 }

/-- The parameter factor `∏_v e^{πi p_v τ_v}`. -/
noncomputable def paramFac {S : WaveTurbulence.SumintShape} (p τ : S.TVar → ℝ) : ℂ :=
  ∏ v, Complex.exp (((Real.pi * (p v * τ v) : ℝ) : ℂ) * Complex.I)

/-- The kind-2 factor `∏_i |t₁ⁱ - s₁ⁱ|^{1-3η}` over the bad blocks of kind 2 (as a complex number; `kind2Factor` of the datum). -/
noncomputable def k2c {S : WaveTurbulence.SumintShape} (bk : Fin S.I → Fin 4) (η : ℝ) (τ : S.TVar → ℝ) : ℂ :=
  ∏ i, (if h : S.nor i = false ∧ bk i = 2 ∧ 0 < S.m i then
    ((|τ (.inl ⟨i, ⟨1, by omega⟩⟩) - τ (.inr (.inl ⟨i, ⟨0, h.2.2⟩⟩))| ^ (1 - 3 * η) : ℝ) : ℂ) else 1)

/-- The clock of the lower joint `b`: the first clock `t₀⁰` of the assembly. -/
theorem clock_lowerJoint (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (tt : Fin 3 → ℝ)
    (τ : (assemblyShape hM9 B).TVar → ℝ) :
    clLocalClock R tt (assemblyClockEquiv hM9 B τ) b = τ (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩) := by
  have := clLocalClock_slot hM9 B tt τ (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩)
  rwa [assemblyClockAtom_first hM9 B (assemblyShape_I_pos hM9 B)] at this

/-- A parameter vector supported at one clock gives one modulation. -/
theorem paramFac_single {S : WaveTurbulence.SumintShape} (v₀ : S.TVar) (lam : ℝ) (p τ : S.TVar → ℝ)
    (hp : ∀ v, p v = if v = v₀ then lam else 0) :
    paramFac p τ = Complex.exp (((Real.pi * lam * τ v₀ : ℝ) : ℂ) * Complex.I) := by
  classical
  unfold paramFac
  rw [Finset.prod_eq_single v₀ (fun v _ hv => by simp [hp v, hv]) (fun h => (h (Finset.mem_univ _)).elim)]
  simp only [hp v₀, ite_true]
  congr 3
  ring

/-- `signedPhase` splits into the phase without parameters and bad kinds, the parameter factor and the kind-2 factor. -/
theorem signedPhase_split (D : WaveTurbulence.SumintDatum d) (cfs cs : Fin D.S.I → ℤˣ) (L γ δ η : ℝ)
    (x : D.S.VIdx → (Fin d → ℤ)) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) :
    signedPhase D cfs cs L γ δ η x r t τ =
      signedPhase { D with param := fun _ => 0, badKind := fun _ => 0 } cfs cs L γ δ η x r t τ *
        (paramFac D.param τ * k2c D.badKind η τ) := by
  unfold signedPhase paramFac k2c
  have h0 : ∀ i : Fin D.S.I,
      (if h : D.S.nor i = false ∧ (0 : Fin 4) = 2 ∧ 0 < D.S.m i then
        ((|τ (.inl ⟨i, ⟨1, by omega⟩⟩) - τ (.inr (.inl ⟨i, ⟨0, h.2.2⟩⟩))| ^ (1 - 3 * η) : ℝ) : ℂ) else 1) = 1 :=
    fun i => dite_eq_right_iff.mpr (fun h => absurd h.2.1 (by decide))
  simp only [h0, zero_mul, mul_zero, Complex.ofReal_zero, Complex.exp_zero, Finset.prod_const_one, mul_one,
    Fintype.prod_sum_type, Fintype.prod_sigma, Finset.prod_mul_distrib]
  ring

/-- **N2(a): the phase of the engine datum** is the source `signedPhase` without parameters and bad kinds, times the parameter
factor and the kind-2 factor. -/
theorem engDatum_phase (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    (L γ δ η : ℝ) (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)) (r : Mom d) (t : ℝ) (τ : (assemblyShape hM9 B).TVar → ℝ) :
    (engDatum hM9 B hG W wN wDec bk cons g g').phase L γ δ η x r t τ =
      signedPhase (sourceSumintDatum hM9 B hG (W0 W)) (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ δ η x r t τ *
        (paramFac W.param τ * k2c bk η τ) := by
  have e1 : (engDatum hM9 B hG W wN wDec bk cons g g').phase L γ δ η x r t τ =
      signedPhase (sourceSumintDatum hM9 B hG { W with badKind := bk }) (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B)
        L γ δ η x r t τ := rfl
  exact e1.trans ((signedPhase_split (sourceSumintDatum hM9 B hG { W with badKind := bk }) (assemblyCoreFirstSign hM9 B)
    (assemblyCoreSign hM9 B) L γ δ η x r t τ).trans rfl)

/-- **N2(a): the recentring factor times the regional phase is the source `signedPhase`** (at `δ' = 2δ`, the frozen gap `E₀ - E₁`). -/
theorem recFac_mul_regionalPhase (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (base : Mom d)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ)
    (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)) (τ : (assemblyShape hM9 B).TVar → ℝ) :
    recFac (G.sign a.toNode) (G.sign a.toNode) L γ δ tt
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) *
      clRegionalPhase G U L γ δ
        (cosetDecoration G L base (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1))
        (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) =
    signedPhase (sourceSumintDatum hM9 B hG (W0 W)) (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) L γ (2 * δ) η x
      (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
        sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (tt 0) τ := by
  have hrec := clLocalDecoration_phase_recenter B.isBlock R L γ δ base (fun j => base + latticePoint L (β j))
    ((clNormalizedChainEquiv hL B base β hβ hM9).symm x) (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) (tt 0)
  have hsp := assembly_regionalPhase_eq_signedPhase hM9 B hG (W0 W) (fun _ => rfl)
    (fun _ => show (0 : Fin 4) ≠ 2 by decide) hL base β hβ γ δ η x tt τ
  rw [sumintBoundary_gap_physical (L := L) (G.sign a.toNode) base β hβ, ← hsp]
  simp only [recFac, sumintBoundary_invol, clRegionalPhase]
  exact hrec

/-- The scalar identity behind `freeDict_of_rowForm`. -/
theorem dict_scalar {α : Type*} (S : Set α) (τ : α) (f : α → ℂ) (D : Prop) [Decidable D] (c A e P Q m k1 k2 Wp sPh : ℂ)
    (hD1 : τ ∈ S → D) (hD2 : D → τ ∉ S → Q = 0) (hQ : τ ∈ S → Q = k1 * k2 * Wp) (hf : f τ = sPh * (A * k2) * Wp)
    (hm : m = e) (hrec : c * P = sPh) :
    c * (A * (e * ((if D then 1 else 0) * (P * Q)))) = m * (k1 * S.indicator f τ) := by
  by_cases h : τ ∈ S
  · rw [Set.indicator_of_mem h, hQ h, hf, hm, ← hrec]
    simp only [hD1 h, ite_true]
    ring
  · rw [Set.indicator_of_notMem h]
    by_cases hd : D
    · rw [hD2 hd h]; ring
    · simp only [hd, ite_false]; ring

/-- **N2: the free-domain dictionary from the row form.**  `ψ = e^{πiλu_b} ψ₀` with `ψ₀` in row form; the modulation is the engine
parameter `λ` at the clock `t₀⁰` of `b` (`hpar`); `hMx` (the sign), `hsub`/`hvan` (time domain) and `hrow` (rows) as in the module docstring. -/
theorem freeDict_of_rowForm (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (base : Mom d)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ)
    (ψ ψ0 : PsiT G d) (lam : ℝ)
    (hψ : ∀ x t u, ψ x t u = Complex.exp (((Real.pi * lam * u b : ℝ) : ℂ) * Complex.I) * ψ0 x t u)
    {Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop}
    {Qw : SourcePair G → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ}
    {Tw : GBranch G.tree → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ}
    (hR : RowForm hG R L γ δ base ψ0 Dm Qw Tw)
    (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    (Mx : CharMix (assemblyShape hM9 B) d) (cr : ClockedRows3 (engDatum hM9 B hG W wN wDec bk cons g g'))
    (hpar : ∀ v, W.param v =
      if v = (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩ : (assemblyShape hM9 B).TVar) then lam else 0)
    (hMx : ∀ x, Mx.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x =
      (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) : ℂ))
    (hsub : ∀ᵐ τ : (assemblyShape hM9 B).TVar → ℝ,
      τ ∈ (engDatum hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2) →
        Dm tt (clLocalClock R tt (assemblyClockEquiv hM9 B τ)))
    (hvan : ∀ x, ∀ᵐ τ : (assemblyShape hM9 B).TVar → ℝ, Dm tt (clLocalClock R tt (assemblyClockEquiv hM9 B τ)) →
      τ ∉ (engDatum hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2) →
      (∏ p ∈ clRegionalPairs hG U, Qw p tt (clLocalClock R tt (assemblyClockEquiv hM9 B τ))
          (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)) *
        (∏ v ∈ U.erase a, Tw v tt (clLocalClock R tt (assemblyClockEquiv hM9 B τ))
          (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)) = 0)
    (hrow : ∀ x, ∀ᵐ τ : (assemblyShape hM9 B).TVar → ℝ,
      τ ∈ (engDatum hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_pos hM9 B) (tt 0) (tt 1) (tt 2) →
      (∏ p ∈ clRegionalPairs hG U, Qw p tt (clLocalClock R tt (assemblyClockEquiv hM9 B τ))
          (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)) *
        (∏ v ∈ U.erase a, Tw v tt (clLocalClock R tt (assemblyClockEquiv hM9 B τ))
          (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1)) =
      ((kind1Pref (D := engDatum hM9 B hG W wN wDec bk cons g g')
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) : ℝ) : ℂ) * k2c bk η τ *
        ∏ ρ, cr.W ρ (cr.clock τ tt ρ)
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
            sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1)
          (rowMom (engDatum hM9 B hG W wN wDec bk cons g g') L x
            (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) ρ)) :
    FreeDict hM9 B hG W hL γ δ η base β hβ tt ψ wN wDec bk cons g g' Mx cr := by
  classical
  intro x
  filter_upwards [hsub, hvan x, hrow x] with τ hd1 hd2 hr
  have hform := hR _ ((clNormalizedChainEquiv hL B base β hβ hM9).symm x) tt (clLocalClock R tt (assemblyClockEquiv hM9 B τ))
  have hm := hMx x
  have hrec := recFac_mul_regionalPhase hM9 B hG W hL γ δ η base β hβ tt x τ
  rw [hψ, clock_lowerJoint hM9 B tt τ]
  generalize clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1 = X0 at hform hm hd2 hr hrec ⊢
  rw [hform]
  exact dict_scalar _ τ _ _ _ _ _ _ _ _ _ _ _ _ hd1 hd2 hr
    (by simp only [clockedIntegrand3]; rw [engDatum_phase, paramFac_single _ lam _ τ hpar]) hm hrec

end WaveTurbulence.VineEstS5C.P4.W2
