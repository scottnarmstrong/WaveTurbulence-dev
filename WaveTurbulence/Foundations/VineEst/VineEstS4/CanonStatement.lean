/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Statement
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Canon

/-! # TARGET Proposition `vineest` over canonical representatives (V5 Step 4b, R31(1))

`VineEstCanon P` is the literal form of TARGET's (vineest1)/(vineest2): the skeleton `G` is prime (TARGET
`propstructure2`), and `Σ_{G'} K^U_{(G')}` runs over the canonical representatives of the twist class,
`canonFinset`: for each garden `G'` of the class exactly one (state, region), whose skeleton is `G'_sk` (the unique prime
skeleton, `existsUnique_prime_with_replacements`) with its unique regular replacements.  There is no quantifier over
sections.

* `vineEstCanon_of_full`: `VineEstFull P` (every section) implies it.
* `VineEstFullPrime` is `VineEstFull` with the premise `IsPrimeGarden G`; `vineEstFullPrime_iff_canon` shows that for a
  prime skeleton the two agree: every section is the canonical one (`classSection_eq`), so the kernel sum is independent
  of the representative and the earlier `∀`-sections form is not stronger than TARGET.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  VineParamContract TTree
open scoped ENNReal

/-- **TARGET Proposition `vineest` (L1730-L1752), literal form.**  The sum over LF twists `G'` is the sum over the canonical
representatives of the twist class of the chain `U` of the prime skeleton `G`. -/
@[expose] def VineEstCanon (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D → ∀ {Rin : ℕ → Mom P.d → ℝ}, (∀ r ≤ p, InputRemainder P (Rin r) r) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (_hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (kind : Bool), (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d),
    RowCoherent hM9 B RD hG layer hLayer (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ (inputsF P Rin) p →
    XNorm00Restr (2 * P.η ^ 8) (outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (fun tt E => twistedRecentered (rowSel := VineEst.RowSel.plain) G a (canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B))
        P.L P.γ P.δ (inputsF P Rin) wBar
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) ≤
    ENNReal.ofReal ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7))

/-- `VineEstFull` restricted to prime skeletons (the case of TARGET). -/
@[expose] def VineEstFullPrime (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D → ∀ {Rin : ℕ → Mom P.d → ℝ}, (∀ r ≤ p, InputRemainder P (Rin r) r) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (_hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer), (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d),
    RowCoherent hM9 B RD hG layer hLayer (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ (inputsF P Rin) p →
    ∀ (kind : Bool) (Z : Finset (Σ Bs : FamilyReconstruction w (assemblySourceFamily B).CoreIndex, ChainAt Bs.skeleton Bs.family)),
    ClassSectionK p kind (startState B RD hG layer hLayer) (chainStart B) Z →
    XNorm00Restr (2 * P.η ^ 8) (outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (fun tt E => twistedRecentered (rowSel := VineEst.RowSel.plain) G a Z P.L P.γ P.δ (inputsF P Rin) wBar
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) ≤
    ENNReal.ofReal ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7))

theorem vineEstCanon_of_fullPrime {P : WTParams} (H : VineEstFullPrime P) : VineEstCanon P := by
  intro p hp Rin hRin w G U a b R n hprime hM9 B RD hG layer hLayer kind hlay hrs hl1 centre wBar hcoh
  exact H hp hRin hprime hM9 B RD hG layer hLayer hlay hrs hl1 centre wBar hcoh kind _
    (classSection_canonFinset p kind (A := startState B RD hG layer hLayer) hprime (chainStart B))

theorem vineEstFullPrime_of_canon {P : WTParams} (H : VineEstCanon P) : VineEstFullPrime P := by
  intro p hp Rin hRin w G U a b R n hprime hM9 B RD hG layer hLayer hlay hrs hl1 centre wBar hcoh kind Z hZ
  rw [classSection_eq hprime hZ]
  exact H hp hRin hprime hM9 B RD hG layer hLayer kind hlay hrs hl1 centre wBar hcoh

theorem vineEstFullPrime_iff_canon (P : WTParams) : VineEstFullPrime P ↔ VineEstCanon P :=
  ⟨vineEstCanon_of_fullPrime, vineEstFullPrime_of_canon⟩

theorem vineEstFullPrime_of_full {P : WTParams} (H : VineEstFull P) : VineEstFullPrime P := by
  intro p hp Rin hRin w G U a b R n _hprime
  exact H hp hRin

theorem vineEstCanon_of_full {P : WTParams} (H : VineEstFull P) : VineEstCanon P :=
  vineEstCanon_of_fullPrime (vineEstFullPrime_of_full H)

end WaveTurbulence.VineEstS4
