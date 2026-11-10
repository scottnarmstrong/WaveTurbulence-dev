/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.DegenVine.EpsMix
public import WaveTurbulence.Foundations.Vine.DegenVine.ClockedBoundMixRestr

/-! # The `ε`-weighted vine-chain kernel (DEGEN-VINE, GAP.degenerate.vine)

`clockedExprEps` is V5's `clockedExpr` with the lattice sum weighted by `ε(x) = ∏ᵢ ε(kᵢ¹, kᵢ², kᵢ³)`, each label
`kᵢʲ` being a weight row's momentum or a boundary vector.  `ε` is a character mixture of mass `3^n`
(`exists_eps_mix`), so `clockedBoundMix_of_restr` bounds the `ε`-weighted kernel by `3^n` times the engine bound:
the degenerate decorations (`ε ≠ 1`) cost only the constant `3^n`, and no gain is needed for (vineest2).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.DegenVine
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS3.Eng MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- The label `ρ` (a weight row) or `k` (a boundary vector) as an affine reference. -/
noncomputable def labelRef (D : SumintDatum d) : (Row D ⊕ Fin 4) → AffRef D.S
  | Sum.inl (Sum.inl v) => ⟨fun v' => D.T₁ v v', D.H₁ v, (D.H_coset v).1⟩
  | Sum.inl (Sum.inr v) => ⟨fun v' => D.T₂ v v', D.H₂ v, (D.H_coset v).2⟩
  | Sum.inr k => ⟨fun _ => 0, Pi.single k 1, by simp⟩

/-- The momentum of a label. -/
noncomputable def labMom (D : SumintDatum d) (L : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (E : Fin 4 → Mom d) :
    (Row D ⊕ Fin 4) → Mom d := Sum.elim (rowMom D L x E) E

theorem labelRef_val (D : SumintDatum d) (L : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (E : Fin 4 → Mom d)
    (r : Row D ⊕ Fin 4) : (labelRef D r).val L x E = labMom D L x E r := by
  rcases r with (v | v) | k
  · simp [labelRef, labMom, AffRef.val, CharMix.affVal, rowMom, SumintDatum.kVec]
  · simp [labelRef, labMom, AffRef.val, CharMix.affVal, rowMom, SumintDatum.ℓVec]
  · simp [labelRef, labMom, AffRef.val, CharMix.affVal, Finset.sum_apply, Pi.single_apply]

variable {ι : Type*} [Fintype ι]

/-- `ε(x) = ∏ᵢ ε(kᵢ¹, kᵢ², kᵢ³)`, the coefficient of the vine chain, on physical momenta. -/
noncomputable def epsOf (D : SumintDatum d) (L : ℝ) (l₁ l₂ l₃ : ι → Row D ⊕ Fin 4)
    (x : D.S.VIdx → (Fin d → ℤ)) (E : Fin 4 → Mom d) : ℝ :=
  ∏ i, epsMom (labMom D L x E (l₁ i)) (labMom D L x E (l₂ i)) (labMom D L x E (l₃ i))

/-- V5's `clockedExpr` with the lattice sum weighted by `ε(x)`. -/
noncomputable def clockedExprEps {D : SumintDatum d} (l₁ l₂ l₃ : ι → Row D ⊕ Fin 4) (cr : ClockedRows D)
    (coreFirstSign coreSign : Fin D.S.I → ℤˣ) (hI : 0 < D.S.I) (L γ δ η : ℝ) (tt : Fin 3 → ℝ)
    (E : Fin 4 → Mom d) : ℂ :=
  ∑' x : D.S.VIdx → (Fin d → ℤ), (epsOf D L l₁ l₂ l₃ x E : ℂ) * ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2),
    clockedIntegrand cr coreFirstSign coreSign L γ δ η x E tt τ

theorem XNorm00Restr_mono_of_eq {r : ℕ} {V : Type*} (θ : ℝ) (B : Set (Fin r → ℝ)) (K : Set V)
    (F G : (Fin r → ℝ) → V → ℂ) (h : ∀ t ∈ B, ∀ v ∈ K, F t v = G t v) :
    XNorm00Restr θ B K F ≤ XNorm00Restr θ B K G := by
  unfold XNorm00Restr
  refine le_iInf₂ fun H hH => ?_
  exact iInf₂_le H (fun t ht v hv => (hH t ht v hv).trans (h t ht v hv).symm)

/-- **GAP.degenerate.vine / vineest Step 3 with `ε`.** The `ε`-weighted clocked `sumint` expression obeys the
engine bound with the constant multiplied by `3^n` (`n` = the number of nodes carrying a factor `ε`). -/
theorem clockedBoundEps_of_restr {A : ℝ} {P : WTParams} (hdb : SumintMixDoubledAt A P) (hL : 0 < P.L)
    (hη0 : 0 < P.η) (hη1 : P.η ≤ 1) (hC1 : 0 ≤ P.C₁) (hδ : 0 < P.δ) (hd1 : 1 ≤ P.d)
    {D : SumintDatum P.d} (hI : 0 < D.S.I) (cfs cs : Fin D.S.I → ℤˣ)
    (l₁ l₂ l₃ : ι → Row D ⊕ Fin 4)
    (hno : ∀ i, D.badKind i ≠ 1) (hbad : ∀ i, D.badKind i ≠ 2)
    (hAdm : ∀ (p : D.S.TVar → ℝ) (a b : D.S.VIdx → Mom P.d → ℂ), WeightBounds D P.L P.γ P.η a b →
      ({ D with param := p, wK := a, wL := b } : SumintDatum P.d).Admissible A P.L P.γ P.η P.D)
    (hM : D.S.M ≤ P.N 1 ^ 4) (cr : ClockedRows D)
    (Bx : Row D → Set (Fin 2 → ℝ)) (qx : Row D → Fin 2 → ℝ) (β : Row D → ℝ≥0∞)
    (hbox : ∀ ρ, Bx ρ ⊆ cell (qx ρ)) (hint : ∀ ρ, Bx ρ ⊆ closure (interior (Bx ρ)))
    (hcont : ∀ ρ k, Continuous fun t => cr.W ρ t k)
    (hres : ∀ ρ, XNormRestr (6 * P.η ^ 6) (30 * P.d) (rowOrder D ρ) (Bx ρ) Set.univ (cr.W ρ) < β ρ)
    (hβ : ∀ ρ, β ρ ≠ ⊤)
    (hclock : ∀ tt ∈ outBox D, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2), ∀ ρ, cr.clock τ tt ρ ∈ Bx ρ) :
    ∃ Cfs : ℝ≥0∞, Cfs ≠ ⊤ ∧
      XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
          (fun tt E => clockedExprEps l₁ l₂ l₃ cr cfs cs hI P.L P.γ (2 * P.δ) P.η tt E) ≤
        (ccη P.η + 1) * ENNReal.ofReal ((3 : ℝ) ^ Fintype.card ι *
            (engineConst P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
              ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) *
          ∏ ρ, (Cfs * β ρ) := by
  obtain ⟨N, hmass, hval⟩ := exists_eps_mix (ι := ι) (S := D.S) (L := P.L) hL.ne'
    (fun i => labelRef D (l₁ i)) (fun i => labelRef D (l₂ i)) (fun i => labelRef D (l₃ i)) D.wBar
  obtain ⟨Cfs, hC, hb⟩ := clockedBoundMix_of_restr hdb hL hη0 hη1 hC1 hδ hd1 hI cfs cs N hno hbad hAdm hM cr
    Bx qx β hbox hint hcont hres hβ hclock
  refine ⟨Cfs, hC, ?_⟩
  refine (XNorm00Restr_mono_of_eq _ _ _ _ _ ?_).trans (hb.trans_eq ?_)
  · intro tt htt E hE
    unfold clockedExprEps clockedExprMul
    refine tsum_congr fun x => ?_
    congr 1
    rw [hval E (fun k => (hE.1 k).1) x]
    simp only [epsOf, labelRef_val]
  · rw [hmass]

end WaveTurbulence.DegenVine
